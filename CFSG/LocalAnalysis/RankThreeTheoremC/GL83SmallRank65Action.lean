module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Rep
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

private theorem gl65_mem_centralizer_of_fixing {X : Type} [Group X] {f : ℕ} (hf : f.Prime)
    (hf3 : f ≠ 3) {F : Subgroup X} {D : Subgroup F}
    (hfix : IsPGroup f (fixingSubgroup (MulAut F) (D : Set F))) {r : X}
    (hrN : r ∈ normalizer (F : Set X)) (hr3 : ∃ m : ℕ, r ^ 3 ^ m = 1)
    (hrD : ∀ d ∈ D, (d : X) * r = r * (d : X)) : r ∈ centralizer (F : Set X) := by
  set φ : MulAut F := F.normalizerMonoidHom ⟨r, hrN⟩ with hφ
  have hφapp : ∀ g : F, ((φ g : F) : X) = r * g * r⁻¹ := fun _ => rfl
  have hmem : φ ∈ fixingSubgroup (MulAut F) (D : Set F) := by
    rw [mem_fixingSubgroup_iff (MulAut F)]
    intro d hd
    apply Subtype.ext
    change ((φ d : F) : X) = d
    rw [hφapp, ← hrD d hd, mul_inv_cancel_right]
  obtain ⟨n, hn⟩ := hfix ⟨φ, hmem⟩
  have hn' : φ ^ f ^ n = 1 := congrArg Subtype.val hn
  obtain ⟨m, hm⟩ := hr3
  have hm' : φ ^ 3 ^ m = 1 := by
    have h1 : (⟨r, hrN⟩ : normalizer (F : Set X)) ^ 3 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [hφ, ← map_pow, h1, map_one]
  have hcop : Nat.Coprime (f ^ n) (3 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hf Nat.prime_three).2 hf3)
  have hφ1 : φ = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn')
      (orderOf_dvd_of_pow_eq_one hm')
  rw [mem_centralizer_iff]
  intro x hx
  have h2 : ((φ ⟨x, hx⟩ : F) : X) = x := by rw [hφ1]; rfl
  rw [hφapp] at h2
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

private theorem gl65_conj_mem_map_of_characteristic {X : Type} [Group X] {F : Subgroup X}
    {D : Subgroup F} (hD : D.Characteristic) {r : X} (hrN : r ∈ normalizer (F : Set X)) {k : X}
    (hk : k ∈ D.map F.subtype) : r * k * r⁻¹ ∈ D.map F.subtype := by
  obtain ⟨d, hd, rfl⟩ := mem_map.1 hk
  exact mem_map.2 ⟨F.normalizerMonoidHom ⟨r, hrN⟩ d,
    characteristic_iff_le_comap.mp hD (F.normalizerMonoidHom ⟨r, hrN⟩) hd, rfl⟩

private theorem gl65_commutator_le_centralizer_map {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) (hf3 : f ≠ 3) {F R : Subgroup X} (hR : IsPGroup 3 R)
    (hRF : R ≤ normalizer (F : Set X)) (hrk : CFSG.Open.pRank f F ≤ 2) {D : Subgroup F}
    (hDchar : D.Characteristic) (hDcomm : ⁅D, (⊤ : Subgroup F)⁆ ≤ D ⊓ centralizer (D : Set F))
    (hDexp : ∀ x ∈ D, x ^ f = 1) :
    ⁅R, R⁆ ≤ centralizer ((D.map F.subtype : Subgroup X) : Set X) := by
  have hexp : ∀ d ∈ D.map F.subtype, d ^ f = 1 := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hd
    rw [subtype_apply, ← coe_pow, hDexp y hy, coe_one]
  refine gl65_commutator_le_centralizer_of_exponent hf hf2 hf3 ?_ hexp ?_ hR ?_ ?_
  · intro g
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hexp g g.2
  · rw [commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have h1 : F.subtype ⁅a, b⁆ = ⁅F.subtype a, F.subtype b⁆ := map_commutatorElement F.subtype a b
    have h2 : ⁅a, b⁆ ∈ centralizer (D : Set F) :=
      (hDcomm (commutator_mem_commutator ha (mem_top b))).2
    rw [← h1, ← map_mul, ← map_mul, mem_centralizer_iff.1 h2 c hc]
  · rw [le_normalizer_iff]
    intro r hr k hk
    exact gl65_conj_mem_map_of_characteristic hDchar (hRF hr) hk
  · exact (CFSG.SectionRank.pRank_mono hf.one_lt (map_subtype_le D)).trans hrk

theorem gl65_commutator_le_centralizer {X : Type} [Group X] [Finite X] {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) (hf3 : f ≠ 3) {F R : Subgroup X} (hF : IsPGroup f F) (hR : IsPGroup 3 R)
    (hRF : R ≤ normalizer (F : Set X)) (hrk : CFSG.Open.pRank f F ≤ 2) :
    ⁅R, R⁆ ≤ centralizer (F : Set X) := by
  by_cases hbot : F = ⊥
  · subst hbot
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    have h1 : h = 1 := Subgroup.mem_bot.1 hh
    rw [h1, one_mul, mul_one]
  · have : Fact f.Prime := ⟨hf⟩
    have : Nontrivial F := (nontrivial_iff_ne_bot F).2 hbot
    obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hf2 hF
    have hbb := gl65_commutator_le_centralizer_map hf hf2 hf3 hR hRF hrk hDchar hDcomm hDexp
    rw [commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
    have hcen := hbb (commutator_mem_commutator ha hb)
    refine gl65_mem_centralizer_of_fixing hf hf3 hDfix (hRF hab) ?_ ?_
    · obtain ⟨m, hm⟩ := hR ⟨⁅a, b⁆, hab⟩
      exact ⟨m, congrArg Subtype.val hm⟩
    · intro d hd
      exact mem_centralizer_iff.1 hcen (F.subtype d) (mem_map_of_mem _ hd)

end CFSG.LocalAnalysis.RankThreeTheoremC
