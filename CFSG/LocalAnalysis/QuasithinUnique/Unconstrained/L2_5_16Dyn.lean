module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16Aux
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Dynkin

variable {G : Type} [Group G]

theorem exists_moving_of_dynkin {M S K : Subgroup G} (hSM : S ≤ M)
    (hNP : ∀ P : Subgroup G, IsSylowTwoOf P K → K ⊓ Subgroup.normalizer (P : Set G) ≤ P)
    (hE : ∀ P : Subgroup G, IsSylowTwoOf P K → ∃ E : Subgroup G, E ≤ P ∧ IsFourSubgroup E ∧
      P ≤ Subgroup.normalizer (E : Set G) ∧ K ⊓ Subgroup.normalizer (E : Set G) ≠ K ∧
      ¬ (K ⊓ Subgroup.normalizer (E : Set G) ≤ P))
    (hBor : IsBorelIn (M ⊓ K) K) (hDyn : NontrivialOnDynkin M S K) :
    ∃ P X : Subgroup G, IsSylowTwoOf P K ∧ M ⊓ K = P ∧ P ≤ X ∧ X ≤ K ∧ X ≠ P ∧ X ≠ K ∧
      ∃ s ∈ S ⊓ Subgroup.normalizer (K : Set G),
        s ∈ Subgroup.normalizer (P : Set G) ∧ s ∉ Subgroup.normalizer (X : Set G) := by
  obtain ⟨P, hP, hB⟩ := hBor
  have hPK : P ≤ K := hP.1
  have hBP : M ⊓ K = P := by
    apply le_antisymm
    · rw [hB]; exact hNP P hP
    · rw [hB]
      exact le_inf hPK (Subgroup.le_normalizer)
  obtain ⟨E, hEP, hE4, hPE, hXK, hXP⟩ := hE P hP
  have hPX : P ≤ K ⊓ Subgroup.normalizer (E : Set G) := le_inf hPK hPE
  have hXPne : K ⊓ Subgroup.normalizer (E : Set G) ≠ P := fun h => hXP (h ▸ le_rfl)
  refine ⟨P, K ⊓ Subgroup.normalizer (E : Set G), hP, hBP, hPX, inf_le_left, hXPne, hXK, ?_⟩
  by_contra hcon
  push Not at hcon
  have hall : S ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G) := by
    intro s hs
    apply hcon s hs
    rw [← hBP, Subgroup.mem_normalizer_iff]
    have hsM : s ∈ M := hSM hs.1
    have hsK := Subgroup.mem_normalizer_iff.mp hs.2
    intro h
    constructor
    · rintro ⟨hhM, hhK⟩
      exact ⟨M.mul_mem (M.mul_mem hsM hhM) (M.inv_mem hsM), (hsK h).mp hhK⟩
    · rintro ⟨hhM, hhK⟩
      refine ⟨?_, (hsK h).mpr hhK⟩
      have := M.mul_mem (M.mul_mem (M.inv_mem hsM) hhM) hsM
      simpa [mul_assoc] using this
  rcases hDyn _ (hBP ▸ hPX) inf_le_left hall with h | h
  · exact hXPne (h.trans hBP)
  · exact hXK h

theorem exists_four_subgroup_normal {P : Subgroup G} (e : ↥P ≃* DihedralGroup 4) :
    ∃ E : Subgroup G, E ≤ P ∧ IsFourSubgroup E ∧ P ≤ Subgroup.normalizer (E : Set G) := by
  obtain ⟨E₁, E₂, hE₁, hE₂, h1, h2, hne, hall⟩ :=
    CFSG.QuasithinUnique.D8.exists_two_four_subgroups e
  refine ⟨E₁, hE₁, h1, ?_⟩
  have hindex : (E₁.subgroupOf P).index = 2 := by
    have hc := (E₁.subgroupOf P).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁).toEquiv, h1.2,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hc
    omega
  have : (E₁.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hindex
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hE₁).mp this

end Dynkin

section Shape

variable {G : Type} [Group G]

theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem nonempty_sylow_dihedral_four [Finite G] {K SK P : Subgroup G}
    (hcard : Nat.card K = 168 ∨ Nat.card K = 360) (hSK : IsSylowTwoOf SK K)
    (hP : IsSylowTwoOf P K)
    (hshape : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥SK ≃* DihedralGroup n)) ∨
      Nonempty (↥SK ≃* SemidihedralGroup 4)) :
    Nonempty (↥P ≃* DihedralGroup 4) := by
  have hK8 : twoPart K = 8 := by
    rcases hcard with h | h
    · exact twoPart_eq_eight (b := 21) (by norm_num) (by rw [h])
    · exact twoPart_eq_eight (b := 45) (by norm_num) (by rw [h])
  have hSK8 : Nat.card SK = 8 := hSK.card_eq.trans hK8
  have hSKD : Nonempty (↥SK ≃* DihedralGroup 4) := by
    rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have : 2 * n = 8 := by
        rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv]; exact hSK8
      have hn4 : n = 4 := by omega
      subst hn4
      exact ⟨e⟩
    · exfalso
      have h16 := CFSG.Semidihedral.card 4 (by norm_num)
      rw [← Nat.card_congr e.toEquiv] at h16
      omega
  obtain ⟨e⟩ := hSKD
  obtain ⟨h, -, hh⟩ := hSK.exists_conj hP
  subst hh
  exact ⟨(Subgroup.equivMapOfInjective SK (MulAut.conj h).toMonoidHom
    (MulAut.conj h).injective).symm.trans e⟩

theorem exists_moving_elem [Finite G] {M S K SK : Subgroup G} (hSM : S ≤ M)
    (hcard : Nat.card K = 168 ∨ Nat.card K = 360)
    (hcent : ∀ u : ↥K, u * u = 1 → u ≠ 1 →
      Nat.card (Subgroup.centralizer ({u} : Set ↥K)) = 8)
    (hSK : IsSylowTwoOf SK K)
    (hshape : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥SK ≃* DihedralGroup n)) ∨
      Nonempty (↥SK ≃* SemidihedralGroup 4))
    (hfour : ∀ F : Subgroup G, F ≤ K → IsFourSubgroup F →
      Nonempty (↥(K ⊓ Subgroup.normalizer (F : Set G)) ≃* Equiv.Perm (Fin 4)))
    (hBor : IsBorelIn (M ⊓ K) K) (hDyn : NontrivialOnDynkin M S K) :
    ∃ P X : Subgroup G, IsSylowTwoOf P K ∧ M ⊓ K = P ∧ K ⊓ Subgroup.normalizer (P : Set G) ≤ P ∧
      P ≤ X ∧ X ≤ K ∧ X ≠ P ∧ X ≠ K ∧
      ∃ s ∈ S ⊓ Subgroup.normalizer (K : Set G),
        s ∈ Subgroup.normalizer (P : Set G) ∧ s ∉ Subgroup.normalizer (X : Set G) := by
  have hPD : ∀ P : Subgroup G, IsSylowTwoOf P K → Nonempty (↥P ≃* DihedralGroup 4) :=
    fun P hP => nonempty_sylow_dihedral_four hcard hSK hP hshape
  have hNP : ∀ P : Subgroup G, IsSylowTwoOf P K → K ⊓ Subgroup.normalizer (P : Set G) ≤ P := by
    intro P hP x hx
    obtain ⟨e⟩ := hPD P hP
    have hPK : P ≤ K := hP.1
    let P' : Subgroup ↥K := P.subgroupOf K
    have eP' : ↥P' ≃* DihedralGroup 4 := (Subgroup.subgroupOfEquivOfLe hPK).trans e
    have hn : (⟨x, hx.1⟩ : ↥K) ∈ Subgroup.normalizer (P' : Set ↥K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have := Subgroup.mem_normalizer_iff.mp hx.2 (h : G)
      exact this
    have := normalizer_le_of_dihedral_eight P' eP' hcent hn
    exact this
  have hE : ∀ P : Subgroup G, IsSylowTwoOf P K → ∃ E : Subgroup G, E ≤ P ∧ IsFourSubgroup E ∧
      P ≤ Subgroup.normalizer (E : Set G) ∧ K ⊓ Subgroup.normalizer (E : Set G) ≠ K ∧
      ¬ (K ⊓ Subgroup.normalizer (E : Set G) ≤ P) := by
    intro P hP
    obtain ⟨e⟩ := hPD P hP
    obtain ⟨E, hEP, hE4, hPE⟩ := exists_four_subgroup_normal e
    refine ⟨E, hEP, hE4, hPE, ?_, ?_⟩
    · intro h
      obtain ⟨f⟩ := hfour E (hEP.trans hP.1) hE4
      have h24 : Nat.card ↥(K ⊓ Subgroup.normalizer (E : Set G)) = 24 := by
        rw [Nat.card_congr f.toEquiv, card_perm_four]
      rw [h] at h24
      omega
    · intro h
      obtain ⟨f⟩ := hfour E (hEP.trans hP.1) hE4
      have h24 : Nat.card ↥(K ⊓ Subgroup.normalizer (E : Set G)) = 24 := by
        rw [Nat.card_congr f.toEquiv, card_perm_four]
      have h8 : Nat.card P = 8 := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have := Subgroup.card_le_of_le h
      omega
  obtain ⟨P, X, hP, hMK, hPX, hXK, hXP, hXK', hmov⟩ := exists_moving_of_dynkin hSM hNP hE hBor hDyn
  exact ⟨P, X, hP, hMK, hNP P hP, hPX, hXK, hXP, hXK', hmov⟩

end Shape

section AutOn

variable {G : Type} [Group G]

theorem autOn_eq_top_of_outer [Finite G] {H K P X : Subgroup G} (hKH : K ≤ H)
    (hout : Nat.card (Outer ↥K) ∣ 2)
    (hNP : K ⊓ Subgroup.normalizer (P : Set G) ≤ P) (hPK : P ≤ K) (hPX : P ≤ X) (hXK : X ≤ K)
    {s : G} (hs : s ∈ H ⊓ Subgroup.normalizer (K : Set G))
    (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hsX : s ∉ Subgroup.normalizer (X : Set G)) : autOn H K = ⊤ := by
  classical
  have hmemA : ∀ (g : G) (hgH : g ∈ H) (hgN : g ∈ Subgroup.normalizer (K : Set G)),
      conjAct K ⟨g, hgN⟩ ∈ autOn H K := fun g hgH hgN =>
    ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hgH, rfl⟩
  have hconjAct : ∀ (g : Subgroup.normalizer (K : Set G)) (x : ↥K),
      ((conjAct K g x : ↥K) : G) = (g : G) * x * (g : G)⁻¹ := fun g x => rfl
  have hinner : inner ↥K ≤ autOn H K := by
    rintro _ ⟨k, rfl⟩
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have h := hmemA k (hKH k.2) hkN
    have : MulAut.conj k = conjAct K ⟨k, hkN⟩ := by
      ext x
      show ((k * x * k⁻¹ : ↥K) : G) = (k : G) * x * (k : G)⁻¹
      simp
    rw [this]; exact h
  set σ : MulAut ↥K := conjAct K ⟨s, hs.2⟩ with hσ
  have hσA : σ ∈ autOn H K := hmemA s hs.1 hs.2
  have hσinner : σ ∉ inner ↥K := by
    rintro ⟨k, hk⟩
    have hk' : ∀ x : ↥K, (k : G) * x * (k : G)⁻¹ = s * x * s⁻¹ := by
      intro x
      have := congrArg (fun φ : MulAut ↥K => ((φ x : ↥K) : G)) hk
      simpa [hσ, hconjAct] using this
    have hkP : (k : G) ∈ Subgroup.normalizer (P : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro p hp
      have hpP : p ∈ P := hp
      rw [hk' ⟨p, hPK hpP⟩]
      exact (Subgroup.mem_normalizer_iff.mp hsP p).mp hpP
    have hkX : (k : G) ∈ X := hPX (hNP ⟨k.2, hkP⟩)
    apply hsX
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have hyX : y ∈ X := hy
    have := hk' ⟨y, hXK hyX⟩
    rw [← this]
    exact X.mul_mem (X.mul_mem hkX hyX) (X.inv_mem hkX)
  have hfin : Finite (Outer ↥K) := Nat.finite_of_card_ne_zero (by
    intro h0; rw [h0] at hout; exact absurd (zero_dvd_iff.mp hout) (by norm_num))
  have hle : Nat.card (Outer ↥K) ≤ 2 := Nat.le_of_dvd (by norm_num) hout
  have hσbar : (QuotientGroup.mk σ : Outer ↥K) ≠ 1 := by
    intro h
    exact hσinner ((QuotientGroup.eq_one_iff σ).mp h)
  refine eq_top_iff.mpr fun φ _ => ?_
  by_cases hφ : (QuotientGroup.mk φ : Outer ↥K) = 1
  · exact hinner ((QuotientGroup.eq_one_iff φ).mp hφ)
  · by_cases hφσ : (QuotientGroup.mk φ : Outer ↥K) = QuotientGroup.mk σ
    · have : σ⁻¹ * φ ∈ inner ↥K := by
        rw [← QuotientGroup.eq]; exact hφσ.symm
      have h2 : σ⁻¹ * φ ∈ autOn H K := hinner this
      have := (autOn H K).mul_mem hσA h2
      simpa using this
    · exfalso
      have hcard : 3 ≤ Nat.card (Outer ↥K) := by
        have hinj : Function.Injective
            (fun i : Fin 3 => (![1, QuotientGroup.mk σ, QuotientGroup.mk φ] :
              Fin 3 → Outer ↥K) i) := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
        have := Nat.card_le_card_of_injective _ hinj
        simpa using this
      omega

end AutOn

theorem exists_psl2_seven {K : Type} [Group K] (h : StatedClassicalModel K .PSL 3 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F)
      (_ : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
      Fintype.card F = 7 ∧ ringChar F ≠ 2 ∧ 5 ≤ Fintype.card F := by
  have hL : CFSG.Blueprint.LieModel K .PSL 3 2 1 := Or.inl ⟨by decide, h⟩
  have h7 := CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism K hL
  rcases h7 with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨F, i1, i2, i3, e, hqF, hF, hq5⟩ :=
      CFSG.QuasithinUnique.K1.psl2_model_data (X := K) (p := 7) (f := 1) (by norm_num) hc
    exact ⟨F, i1, i2, i3, e, by simpa using hqF, hF, hq5⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem outer_card_dvd_two_of_L32 {K : Type} [Group K] (h : StatedClassicalModel K .PSL 3 2 1) :
    Nat.card (Outer K) ∣ 2 := by
  obtain ⟨F, _, _, _, e, hq7, -, -⟩ := exists_psl2_seven h
  have hcard : Nat.card F = 7 ^ 1 := by
    rw [Nat.card_eq_fintype_card, hq7]; norm_num
  have := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor (p := 7) (f := 1)
    Nat.prime_seven F hcard).2 K ⟨e⟩
  simpa using this

theorem normal_pGroup_eq_bot_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (N : Subgroup X) [N.Normal]
    (hN : IsPGroup p N) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at hN
    have hX : IsPGroup p X := hN.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnc
    have : Nontrivial X := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have : Nontrivial (Subgroup.center X) := hX.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h2 | h2
    · obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center X)
      rw [h2, Subgroup.mem_bot] at hx
      exact hx1 (Subtype.ext hx)
    · have : a ∈ Subgroup.center X := by rw [h2]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem exists_noncomm_K {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    {hs : UnconstrainedSetting G T M} (N : Notation25 hs) :
    ∃ a b : ↥N.K, a * b ≠ b * a := by
  obtain ⟨-, ⟨⟨-, -, a, b, hab⟩, -⟩⟩ := N.isComp
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hnc : a' * b' ≠ b' * a' := fun h =>
    hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])
  have ha'K : ((a' : ↥N.H) : G) ∈ N.K := Subgroup.mem_subgroupOf.mp a'.2
  have hb'K : ((b' : ↥N.H) : G) ∈ N.K := Subgroup.mem_subgroupOf.mp b'.2
  refine ⟨⟨_, ha'K⟩, ⟨_, hb'K⟩, fun h => hnc ?_⟩
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h')

end CFSG.QuasithinUnique.Unc25K1
