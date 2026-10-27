module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def OutCyc (L : Type) [Group L] : Prop :=
  ∀ P : Subgroup (Outer L), IsPGroup 2 P → IsCyclic ↥P

theorem outCyc_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (h : OutCyc L') :
    OutCyc L := by
  intro P hP
  let ε := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  have hc : IsCyclic ↥(P.map ε.toMonoidHom) := h _ (hP.map ε.toMonoidHom)
  exact (Subgroup.equivMapOfInjective P ε.toMonoidHom ε.injective).isCyclic.mpr hc

theorem outCyc_of_sylow {L : Type} [Group L]
    (h : ∀ S : Sylow 2 (Outer L), IsCyclic ↥(S : Subgroup (Outer L))) : OutCyc L := by
  intro P hP
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have := h S
  exact Subgroup.isCyclic_of_le hS

theorem outCyc_of_card_dvd {L : Type} [Group L] {m : ℕ} (hm : Odd m)
    (h : Nat.card (Outer L) ∣ 2 * m) : OutCyc L := by
  intro P hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Outer L) :=
    Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos h (by have := hm.pos; omega)).ne'
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card ↥P ∣ Nat.card (Outer L) := Subgroup.card_subgroup_dvd_card P
  have h2 : 2 ^ n ∣ 2 * m := hn ▸ hdvd.trans h
  have hn1 : n ≤ 1 := by
    by_contra hlt
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h4 : 4 ∣ 2 * m := (Dvd.intro (2 ^ k) (by ring)).trans h2
    obtain ⟨c, hc⟩ := h4
    obtain ⟨d, hd⟩ := hm
    omega
  refine isCyclic_of_card_dvd_prime (p := 2) ?_
  rw [hn]
  exact (pow_dvd_pow 2 hn1).trans (by simp)

theorem finite_outer (L : Type) [Group L] [Finite L] : Finite (Outer L) := by
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  infer_instance

theorem odd_of_ordProj_two_eq_one {N : ℕ} (hN : N ≠ 0) (h : 2 ^ N.factorization 2 = 1) :
    Odd N := by
  rcases Nat.even_or_odd N with he | ho
  · exfalso
    have h2 : 2 ^ 1 ∣ N := by simpa using even_iff_two_dvd.mp he
    have h3 := (Nat.prime_two.pow_dvd_iff_dvd_ordProj hN).1 h2
    rw [h] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  · exact ho

theorem isCyclic_map_mk_of_outCyc {X : Type} [Group X] {L : Subgroup X} [L.Normal]
    (hC : Subgroup.centralizer (L : Set X) ≤ L) (hout : OutCyc ↥L) {Q : Subgroup X}
    (hQ : IsPGroup 2 Q) : IsCyclic ↥(Q.map (QuotientGroup.mk' L)) := by
  let φ : X →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp MulAut.conjNormal
  have hLφ : L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨⟨x, hx⟩, ?_⟩
    ext y
    simp [MulAut.conjNormal_apply]
  have hφL : φ.ker ≤ L := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    obtain ⟨l, hl⟩ := hx
    have hz : x⁻¹ * (l : X) ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨y, hy⟩ : ↥L) : X)) hl
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at h1
      calc y * (x⁻¹ * (l : X)) = x⁻¹ * (x * y * x⁻¹) * l := by group
        _ = x⁻¹ * ((l : X) * y * (l : X)⁻¹) * l := by rw [← h1]
        _ = x⁻¹ * (l : X) * y := by group
    have hzL : x⁻¹ * (l : X) ∈ L := hC hz
    have : x = (l : X) * (x⁻¹ * (l : X))⁻¹ := by group
    rw [this]
    exact L.mul_mem l.2 (L.inv_mem hzL)
  let ψ : X ⧸ L →* Outer ↥L := QuotientGroup.lift L φ hLφ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.lift_mk] at hy
    exact (QuotientGroup.eq_one_iff x).mpr (hφL (MonoidHom.mem_ker.mpr hy))
  have hmap : (Q.map (QuotientGroup.mk' L)).map ψ = Q.map φ := by
    rw [Subgroup.map_map]
    congr 1
  have hcyc : IsCyclic ↥((Q.map (QuotientGroup.mk' L)).map ψ) := by
    rw [hmap]
    exact hout _ (hQ.map φ)
  exact (Subgroup.equivMapOfInjective _ ψ hψ).isCyclic.mpr hcyc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
