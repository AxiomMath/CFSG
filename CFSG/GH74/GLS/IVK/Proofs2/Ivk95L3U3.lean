module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Z
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint

theorem Ez_conj_mem {J : Type} [Group J] [Finite J] (z : J) :
    ∀ c : J, c * z = z * c → ∀ k ∈ Ez z, c * k * c⁻¹ ∈ Ez z := by
  intro c hc k hk
  obtain ⟨y, hy, rfl⟩ := hk
  have hcz : c ∈ centralizer ({z} : Set J) := mem_centralizer_singleton_iff.mpr hc
  have hch : (layer ↥(centralizer ({z} : Set J))).Characteristic := LocalCores.layer_characteristic
  have hn : (layer ↥(centralizer ({z} : Set J))).Normal := inferInstance
  refine ⟨⟨c, hcz⟩ * y * ⟨c, hcz⟩⁻¹, hn.conj_mem y hy ⟨c, hcz⟩, ?_⟩
  simp

theorem exists_prime_pow_of_hasSL2Model {K : Type} [Group K] {q : ℕ} (hodd : Odd q)
    (hsl : HasSL2Model K (fun r => r = q)) :
    ∃ p' n : ℕ, p'.Prime ∧ p' ≠ 2 ∧ 1 ≤ n ∧ q = p' ^ n ∧ HasSL2Model K (fun r => r = p' ^ n) := by
  obtain ⟨F, _, _, hFq, he⟩ := hsl
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp', hFc⟩ := FiniteField.card F (ringChar F)
  have hq : q = ringChar F ^ (n : ℕ) := by rw [← hFq, Nat.card_eq_fintype_card, hFc]
  have hp2 : ringChar F ≠ 2 := by
    intro h2
    rw [h2] at hq
    have : Even q := by
      rw [hq]
      exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
    exact (Nat.not_even_iff_odd.mpr hodd) this
  refine ⟨ringChar F, n, hp', hp2, n.pos, hq, F, inferInstance, inferInstance, ?_, he⟩
  rw [hFq, hq]

theorem ivk95_l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk95Fam (fun X _ => LieModel X .PSL 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ z hz q hodd hq5 hsl hcyc
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hE : IsLnEps 3 J 1 (p ^ f) := CFSG.GH74.Generic.S1.isLnEps_of_model (Or.inl ⟨rfl, hst⟩)
  obtain ⟨hzK, -, -⟩ := ivk95_z_facts hz hodd hsl hcyc
  obtain ⟨p', n, hp', hp'2, -, hqn, hsl'⟩ := exists_prime_pow_of_hasSL2Model hodd hsl
  have hfe := CFSG.GH74.GLS.Stage4.Rest.field_eq_of_component_L3 hp hp2 hE hp' hp'2 hsl'
    (by rw [← hqn]; omega) hzK hz (Ez_conj_mem z)
  refine ⟨1, Or.inl rfl, ?_⟩
  rw [hqn, ← hfe]
  exact hE

theorem ivk95_u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk95Fam (fun X _ => LieModel X .PSU 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ z hz q hodd hq5 hsl hcyc
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have hE : IsLnEps 3 J (-1) (p ^ f) := CFSG.GH74.Generic.S1.isLnEps_of_model (Or.inr ⟨rfl, hst⟩)
  obtain ⟨hzK, -, -⟩ := ivk95_z_facts hz hodd hsl hcyc
  obtain ⟨p', n, hp', hp'2, -, hqn, hsl'⟩ := exists_prime_pow_of_hasSL2Model hodd hsl
  have hfe := CFSG.GH74.GLS.Stage4.Rest.field_eq_of_component_U3 hp hp2 hE hp' hp'2 hsl'
    (by rw [← hqn]; omega) hzK hz (Ez_conj_mem z)
  refine ⟨-1, Or.inr rfl, ?_⟩
  rw [hqn, ← hfe]
  exact hE

end CFSG.GH74.GLS.IVK.Proofs2
