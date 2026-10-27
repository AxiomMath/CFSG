module

public import CFSG.GH74.Uniqueness.SU.SU7Stmts
public import CFSG.GH74.Uniqueness.SU.SU7Gen
public import CFSG.GH74.Uniqueness.SU.SU5Main

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5

namespace Base

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

omit [Finite G] in
theorem x_mem_S (hconf : Conf18H S M V x z) : x ∈ (S : Subgroup G) := by
  obtain ⟨K, -, -, hsup, -⟩ := hconf.K_ex
  have h : x ∈ zpowers x ⊔ K := Subgroup.mem_sup_left (mem_zpowers x)
  rw [hsup] at h
  exact h.2

omit [Finite G] in
theorem z_mem_S (hconf : Conf18H S M V x z) : z ∈ (S : Subgroup G) := by
  obtain ⟨K, hKle, -, -, hzK, -⟩ := hconf.K_ex
  exact (hKle hzK).2

omit [Finite G] in
theorem x_mul_self (hconf : Conf18H S M V x z) : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rw [hconf.hx, pow_two] at this
  exact this

omit [Finite G] in
theorem z_mul_self (hconf : Conf18H S M V x z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rw [hconf.hz, pow_two] at this
  exact this

omit [Finite G] in
theorem z_ne_one (hconf : Conf18H S M V x z) : z ≠ 1 := by
  intro h
  have := hconf.hz
  rw [h, orderOf_one] at this
  omega

omit [Finite G] in
theorem x_ne_one (hconf : Conf18H S M V x z) : x ≠ 1 := by
  intro h
  have := hconf.hx
  rw [h, orderOf_one] at this
  omega

theorem U_le_S (hH : Hyp184 S U M) : U ≤ (S : Subgroup G) := hH.four.1

theorem U_isE (hH : Hyp184 S U M) : IsE 2 U := ⟨hH.four.2.1, hH.four.2.2⟩

theorem U_norm (hH : Hyp184 S U M) :
    ∀ s ∈ (S : Subgroup G), ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
  intro s hs u hu
  exact (Subgroup.mem_normalizer_iff.1 (hH.normal hs) u).1 hu

omit [Finite G] in
theorem card_le_four_of_mem (hconf : Conf18H S M V x z) {E : Subgroup G}
    (hES : E ≤ (S : Subgroup G)) (hE : Open.IsElemAbelian 2 E) (hxE : x ∈ E) :
    Nat.card E ≤ 4 := by
  classical
  obtain ⟨K, hKle, -, hsup, hzK, hK⟩ := hconf.K_ex
  have hEc := isElemAbelian_iff.1 hE
  have hx2 : x * x = 1 := x_mul_self hconf
  have hKx : ∀ k ∈ K, k * x = x * k := fun k hk =>
    (mem_centralizer_iff.1 (hKle hk).1 x (Set.mem_singleton x)).symm
  have hsub : ∀ e ∈ E, e ∈ ({1, x, z, x * z} : Finset G) := by
    intro e he
    have hmem : e ∈ zpowers x ⊔ K := by
      rw [hsup, Subgroup.mem_inf]
      refine ⟨?_, hES he⟩
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hEc.1 y hxE e he
    obtain ⟨j, k, hk, rfl⟩ := Gen.exists_zpow_mul_of_mem_sup hKx hmem
    have hkE : k ∈ E := by
      have : k = x ^ (-j) * (x ^ j * k) := by group
      rw [this]
      exact E.mul_mem (E.zpow_mem hxE _) he
    have hk2 : k * k = 1 := by rw [← pow_two]; exact hEc.2 k hkE
    have hx2' : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx2]
    have hxj : x ^ j = 1 ∨ x ^ j = x := by
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
      · left; rw [zpow_mul, hx2', one_zpow]
      · right; rw [zpow_add, zpow_mul, hx2', one_zpow, one_mul, zpow_one]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hK k hk hk2 with h | h <;> rcases hxj with h' | h' <;> simp [h, h']
  exact (card_le_card_of_subset_finset hsub).trans Finset.card_le_four

theorem emb_zgen (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) :
    J2Emb (S : Subgroup G) (Tsub S U) x ∧ IsZGen (S : Subgroup G) z := by
  obtain ⟨T', x', hE⟩ := exists_config_of_isJ2Type hcl.typeS
  have hT' : (S : Subgroup G) ⊓ centralizer (U : Set G) = T' :=
    hE.centralizer_normal_four (U_le_S hH) (U_norm hH) (U_isE hH)
  have hTT : Tsub S U = T' := by rw [← hT', Tsub, inf_comm]
  obtain ⟨z', hz'⟩ := hE.exists_zgen
  obtain ⟨hz'2, -⟩ := hE.zgen_facts hz'
  have hzz : z' = z := by
    have hcen : ∀ s ∈ (S : Subgroup G), s * z' = z' * s := fun s hs =>
      ((hz'.2.2 z' hz'.1).2 (Or.inr rfl) s hs).symm
    rcases hconf.z_unique z' hz'.1 hcen (by rw [← pow_two]; exact hz'2) with h | h
    · exact absurd h hz'.2.1
    · exact h
  have hz : IsZGen (S : Subgroup G) z := hzz ▸ hz'
  have hF := hE.facts hz'
  obtain ⟨A, B, hL, -, -, -, -, -⟩ := hF.AB
  have hxT : x ∉ Tsub S U := by
    intro hxT
    rw [hTT] at hxT
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact x_mul_self hconf
    rcases hL.invol x hxT (x_ne_one hconf) hx2 with hA | hB
    · have h4 := card_le_four_of_mem hconf (hL.A_le.trans hF.T_le) hL.A_E.1 hA
      rw [hL.A_E.2] at h4
      norm_num at h4
    · have h4 := card_le_four_of_mem hconf (hL.B_le.trans hF.T_le) hL.B_E.1 hB
      rw [hL.B_E.2] at h4
      norm_num at h4
  have hTS : Tsub S U ≤ (S : Subgroup G) := inf_le_right
  exact ⟨J2Emb.of_types hcl.typeS hTS hcl.typeT (x_mem_S hconf) hxT
    (by rw [pow_two]; exact x_mul_self hconf), hz⟩

theorem j2facts (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) : J2Facts (S : Subgroup G) (Tsub S U) x z :=
  (emb_zgen hH hconf hcl).1.facts (emb_zgen hH hconf hcl).2

theorem Zc_eq_U (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) : Zc (Tsub S U) = U :=
  ((j2facts hH hconf hcl).U_unique U (U_le_S hH) (U_norm hH) (U_isE hH)).symm

theorem mem_Zc_iff (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) (g : G) : g ∈ Zc (Tsub S U) ↔ g ∈ U := by
  rw [Zc_eq_U hH hconf hcl]

omit [Finite G] in
theorem mem_Zc_of_normalizer {T : Subgroup G} {a p : G} (ha : a ∈ normalizer (T : Set G))
    (hp : p ∈ Zc T) : a * p * a⁻¹ ∈ Zc T := by
  rw [mem_Zc] at hp ⊢
  refine ⟨(mem_normalizer_iff.1 ha p).1 hp.1, fun t ht => ?_⟩
  have ht' : a⁻¹ * t * a ∈ T := by
    refine (mem_normalizer_iff.1 ha (a⁻¹ * t * a)).2 ?_
    have : a * (a⁻¹ * t * a) * a⁻¹ = t := by group
    rw [this]; exact ht
  have h1 := hp.2 _ ht'
  calc a * p * a⁻¹ * t = a * (p * (a⁻¹ * t * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * t * a) * p) * a⁻¹ := by rw [h1]
    _ = t * (a * p * a⁻¹) := by group

end Base

theorem lemma19AB :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
      (h : Conf18H S M V x z), Hyp184 S U M → Concl189 S U M x h.x_mem →
        ∃ A B R : Subgroup G, Conf19 S U x z A B R := by
  intro G _ _ S U M V x z hconf hH hcl
  have hJ := Base.j2facts hH hconf hcl
  have hZ : Zc (Tsub S U) = U := Base.Zc_eq_U hH hconf hcl
  obtain ⟨A, B, hL, hAx, -, -, -, -⟩ := hJ.AB
  obtain ⟨R, V', hRS, -, hRn, hQ, -, -, -, -, -, hzR, hinv, -, hsq, hfour⟩ := hJ.RV
  have hmemZ : ∀ g, g ∈ Zc (Tsub S U) ↔ g ∈ U := fun g => by rw [hZ]
  have hAB : A ⊓ B = U := by rw [hL.inf_eq, hZ]
  have hUT : U ≤ Tsub S U := fun g hg => by
    have hgZ : g ∈ Zc (Tsub S U) := by rw [hZ]; exact hg
    exact hgZ.1
  have hTS : Tsub S U ≤ (S : Subgroup G) := inf_le_right
  refine ⟨A, B, R, ?_⟩
  exact
  { z_mem := (hmemZ z).1 hJ.z_mem
    isE16_A := ⟨hL.A_E.1, by rw [hL.A_E.2]; norm_num⟩
    isE16_B := ⟨hL.B_E.1, by rw [hL.B_E.2]; norm_num⟩
    A_le := hL.A_le
    B_le := hL.B_le
    AB_inf := hAB
    T_eq := hL.sup_eq
    invol := fun t ht h2 => by
      have h1 : t ≠ 1 := by
        intro h; rw [h, orderOf_one] at h2; omega
      have h3 : t ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one t
      exact hL.invol t ht h1 h3
    B_eq := hAx
    centA := by
      intro a haA haU
      have haB : a ∉ B := fun hB => haU (by rw [← hAB]; exact ⟨haA, hB⟩)
      ext g
      constructor
      · rintro ⟨hgc, hgT⟩
        have hgc' : g * a = a * g := (mem_centralizer_iff.1 hgc a (Set.mem_singleton a)).symm
        exact (hL.cent_A a haA haB g hgT).1 hgc'
      · intro hgA
        refine Subgroup.mem_inf.2 ⟨?_, hL.A_le hgA⟩
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (isElemAbelian_iff.1 hL.A_E.1).1 y haA g hgA
    R_le := hRS
    R_normal := by
      intro s hs
      rw [mem_normalizer_iff]
      intro r
      refine ⟨fun hr => hRn s hs r hr, fun hr => ?_⟩
      have h1 := hRn s⁻¹ ((S : Subgroup G).inv_mem hs) _ hr
      have e : s⁻¹ * (s * r * s⁻¹) * s⁻¹⁻¹ = r := by group
      rw [e] at h1
      exact h1
    R_iso := hQ
    R_invol := fun g hg => by
      have h1 : g ≠ 1 := by
        intro h; rw [h, orderOf_one] at hg; omega
      have h3 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
      constructor
      · intro hgR
        have hgS := hRS hgR
        rcases (hinv g hgS).1 ⟨hgR, h1, h3⟩ with ⟨hgZ, -⟩ | ⟨hgT, -⟩
        · exact Or.inl ((hmemZ g).1 hgZ)
        · exact Or.inr ⟨hgS, hgT⟩
      · rintro (hgU | ⟨hgS, hgT⟩)
        · have hgS : g ∈ (S : Subgroup G) := hTS (hUT hgU)
          exact ((hinv g hgS).2 (Or.inl ⟨(hmemZ g).2 hgU, h1⟩)).1
        · exact ((hinv g hgS).2 (Or.inr ⟨hgT, h3⟩)).1
    R_four := fun g hg => by
      constructor
      · intro hgR
        have hgS := hRS hgR
        exact ⟨hgS, ((hfour g hgS).1 ⟨hgR, hg⟩).2⟩
      · rintro ⟨hgS, hg2⟩
        exact ((hfour g hgS).2 ⟨hg, hg2⟩).1 }

end CFSG.GH74.Uniqueness.SU.SU7
