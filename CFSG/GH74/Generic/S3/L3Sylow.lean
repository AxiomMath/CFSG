module

public import CFSG.GH74.Generic.S3.Nbhd
public import CFSG.GH74.Generic.Context
public import CFSG.GH74.KGroups.L3EpsSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_apply_mk normalizerAct_of_mem
  mem_centralizer_of_normalizerAct_eq_one pow_card_centralizer_eq_one coe_conjOn)

section Quotient

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem eq_one_of_mem_pGroup_of_mem_center_odd {Q : Subgroup L} (hQ : IsPGroup 2 Q)
    (hodd : Odd (Nat.card (center L))) {z : L} (hzQ : z ∈ Q) (hzZ : z ∈ center L) : z = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨z, hzQ⟩
  have h1 : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : z ^ Nat.card (center L) = 1 := pow_card_centralizer_eq_one hzZ
  have h3 : Nat.Coprime (2 ^ k) (Nat.card (center L)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h4 : z ^ Nat.gcd (2 ^ k) (Nat.card (center L)) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [Nat.Coprime.gcd_eq_one h3, pow_one] at h4

theorem isMax_map_center (Q : Sylow 2 L) (hodd : Odd (Nat.card (center L))) :
    IsPGroup 2 ((Q : Subgroup L).map (QuotientGroup.mk' (center L))) ∧
      ∀ T : Subgroup (L ⧸ center L), IsPGroup 2 T →
        (Q : Subgroup L).map (QuotientGroup.mk' (center L)) ≤ T →
          T ≤ (Q : Subgroup L).map (QuotientGroup.mk' (center L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* L ⧸ center L := QuotientGroup.mk' (center L) with hπ
  refine ⟨Q.isPGroup'.map π, ?_⟩
  have hinj : Function.Injective (π.comp (Q : Subgroup L).subtype) := by
    intro a b hab
    have h1 : π (a : L) = π (b : L) := hab
    have h2 : (a : L)⁻¹ * (b : L) ∈ center L := QuotientGroup.eq.1 h1
    have h3 : (a : L)⁻¹ * (b : L) ∈ (Q : Subgroup L) := Q.mul_mem (Q.inv_mem a.2) b.2
    have h4 := eq_one_of_mem_pGroup_of_mem_center_odd Q.isPGroup' hodd h3 h2
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hrange : (π.comp (Q : Subgroup L).subtype).range = (Q : Subgroup L).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardS : Nat.card ((Q : Subgroup L).map π) = Nat.card (Q : Subgroup L) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcardL : Nat.card L = Nat.card (L ⧸ center L) * Nat.card (center L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
  have hfact : (Nat.card (L ⧸ center L)).factorization 2 = (Nat.card L).factorization 2 := by
    have hX0 : Nat.card (L ⧸ center L) ≠ 0 := Nat.card_pos.ne'
    have hZ0 : Nat.card (center L) ≠ 0 := Nat.card_pos.ne'
    rw [hcardL, Nat.factorization_mul hX0 hZ0]
    simp only [Finsupp.add_apply]
    have : (Nat.card (center L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h2
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2))
    rw [this, add_zero]
  have hcard : Nat.card ((Q : Subgroup L).map π) =
      2 ^ (Nat.card (L ⧸ center L)).factorization 2 := by
    rw [hcardS, hfact]
    exact Q.card_eq_multiplicity
  let P : Sylow 2 (L ⧸ center L) := Sylow.ofCard ((Q : Subgroup L).map π) hcard
  intro T hT hST
  have := P.is_maximal' hT hST
  exact this.le

end Quotient

theorem b_L3_sylow : B_L3_sylow := by
  intro G _ _ t p f ht hp hp2 h5 L hLq hodd hmod R hR
  have hLperf : Group.IsPerfect ↥L := hLq.1
  obtain ⟨Q, hQ⟩ := hR
  set π : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπ
  set S : Subgroup (↥L ⧸ center ↥L) := (Q : Subgroup ↥L).map π with hS
  obtain ⟨hS2, hSmax⟩ := isMax_map_center Q hodd
  have hX : StatedClassicalModel (↥L ⧸ center ↥L) t 3 p f := by
    rcases ht with rfl | rfl
    · exact stated_of_lieModel_PSL hmod
    · exact stated_of_lieModel_PSU hmod
  have hRL : R ≤ L := by
    rw [← hQ]
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hlift : ∀ x ∈ R, ∃ q : ↥L, q ∈ (Q : Subgroup ↥L) ∧ (q : G) = x := by
    intro x hx
    rw [← hQ] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq, rfl⟩
  have hmemR : ∀ q : ↥L, q ∈ (Q : Subgroup ↥L) → (q : G) ∈ R := by
    intro q hq
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hQ2 : IsPGroup 2 (Q : Subgroup ↥L) := Q.isPGroup'
  have hQZ : ∀ z : ↥L, z ∈ (Q : Subgroup ↥L) → z ∈ center ↥L → z = 1 :=
    fun z hzQ hzZ => eq_one_of_mem_pGroup_of_mem_center_odd hQ2 hodd hzQ hzZ
  have hπQ : ∀ a b : ↥L, a ∈ (Q : Subgroup ↥L) → b ∈ (Q : Subgroup ↥L) → π a = π b → a = b := by
    intro a b ha hb hab
    have h2 : a⁻¹ * b ∈ center ↥L := QuotientGroup.eq.1 hab
    have h3 : a⁻¹ * b ∈ (Q : Subgroup ↥L) := Q.mul_mem (Q.inv_mem ha) hb
    exact inv_mul_eq_one.1 (hQZ _ h3 h2)
  obtain ⟨hcyc, hexpL, hexpU⟩ := KGroups.L3Eps.l3eps_center_sylow ht hp2 hX hS2 hSmax
  have hle : R ⊓ centralizer (R : Set G) ≤ L := inf_le_left.trans hRL
  let ι : ↥(R ⊓ centralizer (R : Set G)) →* ↥L := Subgroup.inclusion hle
  let ρ : ↥(R ⊓ centralizer (R : Set G)) →* (↥L ⧸ center ↥L) := π.comp ι
  have hιQ : ∀ a : ↥(R ⊓ centralizer (R : Set G)), ι a ∈ (Q : Subgroup ↥L) := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hlift a a.2.1
    have : ι a = q := Subtype.ext hqa.symm
    rw [this]; exact hq
  have hρmem : ∀ a : ↥(R ⊓ centralizer (R : Set G)),
      ρ a ∈ S ⊓ centralizer (S : Set (↥L ⧸ center ↥L)) := by
    intro a
    refine Subgroup.mem_inf.2 ⟨⟨ι a, hιQ a, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hc := (Subgroup.mem_centralizer_iff.1 a.2.2) (q : G) (hmemR q hq)
    show π q * π (ι a) = π (ι a) * π q
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hc
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have := hπQ _ _ (hιQ a) (hιQ b) hab
    exact Subgroup.inclusion_injective hle this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_injective (ρ.codRestrict _ hρmem) (fun a b hab => hρinj (congrArg Subtype.val hab))
  · intro hPSL z hz
    have h1 := hexpL hPSL (ρ ⟨z, hz⟩) (hρmem ⟨z, hz⟩)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_injective ρ hρinj ⟨z, hz⟩, Subgroup.orderOf_mk] at h2
    exact h2
  · intro hPSU z hz
    have h1 := hexpU hPSU (ρ ⟨z, hz⟩) (hρmem ⟨z, hz⟩)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_injective ρ hρinj ⟨z, hz⟩, Subgroup.orderOf_mk] at h2
    exact h2
  ·
    intro A hAN hA2 hAR a ha
    obtain ⟨k, hk⟩ := hA2 ⟨a, ha⟩
    have hak : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
    let an : ↥(normalizer (L : Set G)) := ⟨a, hAN ha⟩
    have hank : an ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hak)
    have hφk : (normalizerAct L an) ^ 2 ^ k = 1 := by rw [← map_pow, hank, map_one]
    have hφS : ∀ s ∈ S, normalizerAct L an s = s := by
      rintro _ ⟨q, hq, rfl⟩
      show normalizerAct L an (QuotientGroup.mk q) = QuotientGroup.mk q
      rw [normalizerAct_apply_mk]
      congr 1
      apply Subtype.ext
      rw [coe_conjOn]
      have := hAR a ha (q : G) (hmemR q hq)
      show a * (q : G) * a⁻¹ = q
      rw [this]; group
    obtain ⟨z', hz'S, hz'c, hz'⟩ := KGroups.L3Eps.l3eps_sylow_aut ht hp2 h5 hX hS2 hSmax hφk hφS
    obtain ⟨zL, hzLQ, rfl⟩ := hz'S
    have hzR : (zL : G) ∈ R ⊓ centralizer (R : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hmemR zL hzLQ, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro r hr
      obtain ⟨q, hq, rfl⟩ := hlift r hr
      have h1 := hz'c (π q) ⟨q, hq, rfl⟩
      have h2 : π (q * zL) = π (zL * q) := by rw [map_mul, map_mul]; exact h1
      have h3 : (q * zL)⁻¹ * (zL * q) ∈ center ↥L := QuotientGroup.eq.1 h2
      have h4 : (q * zL)⁻¹ * (zL * q) ∈ (Q : Subgroup ↥L) :=
        Q.mul_mem (Q.inv_mem (Q.mul_mem hq hzLQ)) (Q.mul_mem hzLQ hq)
      have h5' := hQZ _ h4 h3
      exact congrArg Subtype.val (inv_mul_eq_one.1 h5')
    refine ⟨(zL : G), hzR, ?_⟩
    have hzn : normalizerAct L ⟨(zL : G), Subgroup.le_normalizer zL.2⟩ = MulAut.conj (π zL) :=
      normalizerAct_of_mem L zL.2
    have h1 : normalizerAct L (an * ⟨(zL : G), Subgroup.le_normalizer zL.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hzn, ← hz', mul_inv_cancel]
    exact mem_centralizer_of_normalizerAct_eq_one L h1

end CFSG.GH74.Generic.S3
