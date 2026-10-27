module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartCKlein
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCTwo

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup PartC

theorem hsQ_hypotheses (hEmb : EmbedStmt) (hAut : AutStmt) {G : Type} [Group G] [Finite G]
    {z : G} (hset : HSSetting G z) (hti : HSTI z) {T V : Subgroup G} (hV : HSV z T V) :
    ∃ ι : Qbar z →* Equiv.Perm (Fin 6), Function.Injective ι ∧
      (∀ N : Subgroup (Qbar z), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      ∃ a : Qbar z, orderOf a = 2 ∧
        (∀ x y : Qbar z, orderOf ((x * a * x⁻¹) * (y * a * y⁻¹)) ≠ 4) ∧
        (∃ x y : Qbar z, (x * a * x⁻¹) * (y * a * y⁻¹) = (y * a * y⁻¹) * (x * a * x⁻¹) ∧
          x * a * x⁻¹ ≠ y * a * y⁻¹ ∧
          ∃ w : Qbar z, (x * a * x⁻¹) * (y * a * y⁻¹) = w * a * w⁻¹) := by
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  obtain ⟨ι, hι⟩ := exists_injective_iota hEmb hz hZ4 hF2
  obtain ⟨t₁, ht₁, t₂, ht₂, n1, nz1, n2, nz2, d12, d12'⟩ :=
    exists_independent (z := z) hV.card_eq
  obtain ⟨n3, nz3, hcom, hne, hmul⟩ :=
    klein_four hD hz hF2 hti hV ht₁ ht₂ n1 nz1 n2 nz2 d12 d12'
  have hD1 : t₁ ∈ Dinv z := mem_Dinv_of_mem_V hV ht₁ n1 nz1
  have hnotz : ∀ t : G, t ≠ 1 → t ≠ z → t ∉ Subgroup.zpowers z := fun t h1 h2 h =>
    (Width.mem_zpowers_involution hz h).elim h1 h2
  have hAut' := hAut hset hV
  obtain ⟨m₂, hm₂H, -, hm₂⟩ := hAut'.2.2 t₁ t₂ ht₁ ht₂ (hnotz _ n1 nz1) (hnotz _ n2 nz2)
  obtain ⟨m₃, hm₃H, -, hm₃⟩ := hAut'.2.2 t₁ (t₁ * t₂) ht₁ (V.mul_mem ht₁ ht₂)
    (hnotz _ n1 nz1) (hnotz _ n3 nz3)
  have e2 : qmk z ⟨m₂, hm₂H⟩ * yBar z t₁ * (qmk z ⟨m₂, hm₂H⟩)⁻¹ = yBar z t₂ := by
    rw [← yBar_conj hD hz hF2 hti hD1 ⟨m₂, hm₂H⟩]
    exact congrArg (yBar z) hm₂
  have e3 : qmk z ⟨m₃, hm₃H⟩ * yBar z t₁ * (qmk z ⟨m₃, hm₃H⟩)⁻¹ = yBar z (t₁ * t₂) := by
    rw [← yBar_conj hD hz hF2 hti hD1 ⟨m₃, hm₃H⟩]
    exact congrArg (yBar z) hm₃
  refine ⟨ι, hι, O2_quotient_trivial hF2, yBar z t₁,
    orderOf_yBar hD hz hF2 hti hD1, ?_, ?_⟩
  · intro x y
    obtain ⟨v, hv, hxv⟩ := exists_yBar_conj hD hz hF2 hti hD1 x
    obtain ⟨v', hv', hyv⟩ := exists_yBar_conj hD hz hF2 hti hD1 y
    rw [hxv, hyv]
    exact orderOf_yBar_mul_ne_four hD hz hF2 hti hv hv'
  · refine ⟨1, qmk z ⟨m₂, hm₂H⟩, ?_, ?_, qmk z ⟨m₃, hm₃H⟩, ?_⟩
    · rw [e2, inv_one, one_mul, mul_one]
      exact hcom
    · rw [e2, inv_one, one_mul, mul_one]
      exact hne
    · rw [e2, e3, inv_one, one_mul, mul_one]
      exact hmul.symm

end CFSG.GF2Type.Aschbacher1976Full.HS
