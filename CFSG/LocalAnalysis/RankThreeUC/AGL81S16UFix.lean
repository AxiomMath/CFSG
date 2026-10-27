module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Lift
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Data
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix

variable {G : Type} [Group G] [Finite G]

theorem prime_ne_two_of_dvd_two_pow_add_one {n p : ℕ} (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) :
    p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have : 2 ∣ 1 := (Nat.dvd_add_right h2).mp hpq
  omega

theorem U4NatData.exists_lift_fixing {n p : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)
    (hp : p.Prime) (hp2 : p ≠ 2) (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) {v : G}
    (hv : v ∈ V) {k : ℕ} (E : Subgroup (GL (Fin 4) d.F)) (hE : E ≤ StatedSU 4 (2 ^ n) d.F)
    (hEa : IsElemAbelian p E) (hk : Nat.card E = p ^ k)
    (hfix : ∀ g ∈ E, ((g : GL (Fin 4) d.F) : Matrix (Fin 4) (Fin 4) d.F) *ᵥ
      Multiplicative.toAdd (d.φ ⟨v, hv⟩) = Multiplicative.toAdd (d.φ ⟨v, hv⟩)) :
    ∃ S : Subgroup G, S ≤ M ⊓ centralizer ({v} : Set G) ∧ IsElemAbelian p S ∧
      Nat.card S = p ^ k := by
  set f : ↥L →* GL (Fin 4) d.F := (StatedSU 4 (2 ^ n) d.F).subtype.comp d.ε with hf
  have hker : IsPGroup 2 ↥f.ker := by
    have h : f.ker = CFSG.pCore 2 ↥L := by
      rw [hf, MonoidHom.ker_comp_of_injective _ _ (StatedSU 4 (2 ^ n) d.F).subtype_injective,
        d.ε_ker]
    rw [h]
    exact CFSG.pCore_isPGroup
  have hEf : E ≤ f.range := by
    intro g hg
    obtain ⟨l, hl⟩ := d.ε_surj ⟨g, hE hg⟩
    exact ⟨l, congrArg Subtype.val hl⟩
  obtain ⟨S, hSa, hSc, hSm⟩ := exists_elemAbelian_lift_of_ker f hker hp hp2 hEa hEf
  refine ⟨S.map L.subtype, ?_, IsElemAbelian.map hSa _, ?_⟩
  · intro x hx
    obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hx
    have hsL : (s : G) ∈ L := s.2
    refine ⟨hLM hsL, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hfs : f s ∈ E := hSm ▸ Subgroup.mem_map_of_mem f hsS
    have hfix' := hfix (f s) hfs
    have hv' : (s : G) * v * (s : G)⁻¹ ∈ V :=
      (mem_normalizer_iff.mp (hMV (hLM hsL)) v).mp hv
    have heq := d.equiv s ⟨v, hv⟩ ⟨_, hv'⟩ rfl
    have h1 : d.φ ⟨_, hv'⟩ = d.φ ⟨v, hv⟩ := by
      rw [heq]
      have e : ((d.ε s : ↥(StatedSU 4 (2 ^ n) d.F)) : GL (Fin 4) d.F) = f s := rfl
      rw [e, hfix', ofAdd_toAdd]
    have h2 : (⟨(s : G) * v * (s : G)⁻¹, hv'⟩ : ↥V) = ⟨v, hv⟩ := d.φ_bij.1 h1
    have h3 : (s : G) * v * (s : G)⁻¹ = v := congrArg Subtype.val h2
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc v * (s : G) = ((s : G) * v * (s : G)⁻¹) * (s : G) := by rw [h3]
      _ = (s : G) * v := by group
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hSc, hk]

theorem U4NatData.nonsing_good {n p : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ v ∈ V, v ≠ 1 → ¬ d.sing v →
      2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1 hns
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  have hsum : ∑ i, (Multiplicative.toAdd (d.φ ⟨v, hv⟩)) i ^ (2 ^ n + 1) ≠ 0 :=
    fun h => hns ⟨hv, h⟩
  obtain ⟨E, hEle, hE, hEc, hEfix⟩ :=
    exists_stab_elemAbelian_nonsing hp hpq d.card_F hsum
  obtain ⟨S, hS, hSa, hSc⟩ := d.exists_lift_fixing hp hp2 hLM hMV hv E hEle hE hEc hEfix
  exact CFSG.SectionRank.le_pRank hp.one_lt hS hSa hSc

theorem U4NatData.p_dvd {n p : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ v ∈ V, v ≠ 1 → p ∣ Nat.card ↥(M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1
  have hp2 := prime_ne_two_of_dvd_two_pow_add_one hn hpq
  have hw : Multiplicative.toAdd (d.φ ⟨v, hv⟩) ≠ 0 := by
    intro h
    have h1 : d.φ ⟨v, hv⟩ = 1 := by
      rw [← ofAdd_toAdd (d.φ ⟨v, hv⟩), h]
      rfl
    have h2 : (⟨v, hv⟩ : ↥V) = 1 := d.φ_bij.1 (h1.trans (map_one d.φ).symm)
    exact hv1 (congrArg Subtype.val h2)
  obtain ⟨E, hEle, hE, hEc, hEfix⟩ := exists_stab_elemAbelian_ne_zero hp hpq d.card_F hw
  obtain ⟨S, hS, hSa, hSc⟩ := d.exists_lift_fixing hp hp2 hLM hMV hv E hEle hE hEc hEfix
  have := Subgroup.card_dvd_of_le hS
  rwa [hSc, pow_one] at this

end CFSG.LocalAnalysis.RankThreeUC
