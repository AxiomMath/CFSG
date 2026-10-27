module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigReduce
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Generation

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem inf_eq_bot_of_two_odd [Finite G] {E O : Subgroup G} (hE : IsPGroup 2 E)
    (hO : Odd (Nat.card O)) :
    E ⊓ O = ⊥ := by
  obtain ⟨a, ha⟩ := hE.exists_card_eq
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [ha]
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hO)

theorem map_conj_mul (g h : G) (H : Subgroup G) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem normalizer_sup_odd_le [Finite G] {E O : Subgroup G} [hOn : O.Normal]
    (hE : IsPGroup 2 E) (hO : Odd (Nat.card O)) :
    normalizer ((E ⊔ O : Subgroup G) : Set G) ≤ normalizer (E : Set G) ⊔ O := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  set K := E ⊔ O with hK
  have hcardK : Nat.card K = Nat.card E * Nat.card O := by
    have hEN : E ≤ normalizer (O : Set G) := by
      rw [normalizer_eq_top_iff.mpr hOn]
      exact le_top
    have h := Sol78.card_sup_mul_card_inf' hEN
    rw [inf_eq_bot_of_two_odd hE hO, Subgroup.card_bot, mul_one] at h
    exact h
  set φ := MulAut.conj x with hφ
  have hKx : K.map φ.toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hx
  set E' := E.map φ.toMonoidHom with hE'def
  have hEK : E ≤ K := le_sup_left
  have hE'K : E' ≤ K := hKx ▸ map_mono hEK
  have hcardE' : Nat.card E' = Nat.card E := card_map_of_injective φ.injective
  obtain ⟨a, ha⟩ := hE.exists_card_eq
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hfact : (Nat.card K).factorization 2 = a := by
    rw [hcardK, ha, Nat.factorization_mul (by positivity) (by omega),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by
      intro h2
      exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2)), add_zero]
  let P1 : Sylow 2 K := Sylow.ofCard (E.subgroupOf K) (by
    rw [hfact, ← ha]
    exact Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv)
  let P2 : Sylow 2 K := Sylow.ofCard (E'.subgroupOf K) (by
    rw [hfact, ← ha, ← hcardE']
    exact Nat.card_congr (subgroupOfEquivOfLe hE'K).toEquiv)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P1 P2
  have hkE : E.map (MulAut.conj (k : G)).toMonoidHom = E' := by
    have h0 : ((k • P1 : Sylow 2 K) : Subgroup K) =
        (E.subgroupOf K).map (MulAut.conj k).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have h1 : (((k • P1 : Sylow 2 K) : Subgroup K)).map K.subtype =
        ((P2 : Sylow 2 K) : Subgroup K).map K.subtype := by rw [hk]
    rw [h0] at h1
    have h2 : ((P2 : Sylow 2 K) : Subgroup K).map K.subtype = E' := by
      simp only [P2, Sylow.coe_ofCard]
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hE'K]
    rw [h2] at h1
    rw [← h1]
    ext g
    simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
      mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨k * ⟨y, hEK hy⟩ * k⁻¹, ⟨⟨y, hEK hy⟩, hy, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp⟩
  obtain ⟨e, he, o, ho, heo⟩ := mem_sup_of_normal_right.mp k.2
  have ho' : e * o * e⁻¹ ∈ O := hOn.conj_mem o ho e
  have hk' : (k : G) = (e * o * e⁻¹) * e := by rw [← heo]; group
  have hconjE : E.map (MulAut.conj e).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer he)
  set o' := e * o * e⁻¹ with ho'def
  have hEo : E.map (MulAut.conj o').toMonoidHom = E' := by
    rw [← hkE, hk', map_conj_mul o' e E, hconjE]
  have hnx : o'⁻¹ * x ∈ normalizer (E : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change E.map (MulAut.conj (o'⁻¹ * x)).toMonoidHom = E
    rw [map_conj_mul o'⁻¹ x E]
    change E'.map (MulAut.conj o'⁻¹).toMonoidHom = E
    rw [← hEo, ← map_conj_mul o'⁻¹ o' E, inv_mul_cancel]
    ext g
    simp
  have hx' : x = o' * (o'⁻¹ * x) := by group
  rw [hx']
  exact mul_mem (mem_sup_right ho') (mem_sup_left hnx)

theorem normalizer_sup_normalizer_sup_odd_eq_top [Finite G] {Q : Type*} [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (hO : Odd (Nat.card π.ker)) {E F : Subgroup G}
    (hE : IsPGroup 2 E) (hF : IsPGroup 2 F)
    (h : normalizer ((E.map π : Subgroup Q) : Set Q) ⊔
      normalizer ((F.map π : Subgroup Q) : Set Q) = ⊤) :
    normalizer (E : Set G) ⊔ normalizer (F : Set G) ⊔ π.ker = ⊤ := by
  have key : ∀ A : Subgroup G, IsPGroup 2 A →
      (normalizer ((A.map π : Subgroup Q) : Set Q)).comap π ≤ normalizer (A : Set G) ⊔ π.ker := by
    intro A hA
    rw [comap_normalizer_eq_of_surjective _ hπ, comap_map_eq]
    exact normalizer_sup_odd_le hA hO
  rw [eq_top_iff]
  calc (⊤ : Subgroup G) = (⊤ : Subgroup Q).comap π := comap_top π |>.symm
    _ = (normalizer ((E.map π : Subgroup Q) : Set Q)).comap π ⊔
        (normalizer ((F.map π : Subgroup Q) : Set Q)).comap π := by
      rw [← h, comap_sup_eq _ _ _ hπ]
    _ ≤ (normalizer (E : Set G) ⊔ π.ker) ⊔ (normalizer (F : Set G) ⊔ π.ker) :=
      sup_le_sup (key E hE) (key F hF)
    _ ≤ normalizer (E : Set G) ⊔ normalizer (F : Set G) ⊔ π.ker := by
      refine sup_le (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left

theorem card_map_of_inf_ker {Q : Type*} [Group Q] (f : G →* Q) (A : Subgroup G)
    (h : A ⊓ f.ker = ⊥) : Nat.card (A.map f) = Nat.card A := by
  have hinj : Function.Injective (f.comp A.subtype) := by
    intro a b hab
    have hk : ((a : G))⁻¹ * b ∈ A ⊓ f.ker := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem a.2) b.2, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.mpr hab
    rw [h, mem_bot, inv_mul_eq_one] at hk
    exact Subtype.ext hk
  have hr : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem map_normalizer_subgroupOf_le {H K : Subgroup G} (hHK : H ≤ K) :
    (normalizer ((H.subgroupOf K : Subgroup K) : Set K)).map K.subtype ≤
      normalizer (H : Set G) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := hg
  have hx' : x ∈ normalizer ((H.subgroupOf K : Subgroup K) : Set K) := hx
  rw [mem_normalizer_iff] at hx' ⊢
  intro h
  by_cases hhK : h ∈ K
  · have h1 := hx' ⟨h, hhK⟩
    simpa only [SetLike.mem_coe, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_subtype] using h1
  · constructor
    · intro h1
      exact absurd (hHK h1) hhK
    · intro h1
      exfalso
      apply hhK
      have h2 : (x : G) * h * (x : G)⁻¹ ∈ K := hHK h1
      have h3 := K.mul_mem (K.mul_mem (K.inv_mem x.2) h2) x.2
      simpa [mul_assoc] using h3

theorem le_normalizer_sup_normalizer_sup_core {X : Type} [Group X] [Finite X] {J : Subgroup X}
    {n : ℕ} (hn : 9 ≤ n) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n))
    {E F : Subgroup X} (hEJ : E ≤ J) (hFJ : F ≤ J) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hF2 : ∀ x ∈ F, x ^ 2 = 1) {DE DF : Finset (Fin n)}
    (hDE : DE.card = 4) (hDF : DF.card = 4) (hdisj : Disjoint DE DF)
    (hEs : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ DE,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω)
    (hFs : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) :
    J ≤ normalizer (E : Set X) ⊔ normalizer (F : Set X) ⊔ (pPrimeCore 2 J).map J.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : J →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 J))
  have hker : π.ker = pPrimeCore 2 J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (pPrimeCore 2 J) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hO : Odd (Nat.card π.ker) := by
    rw [hker]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have himg : ∀ A : Subgroup X, A ≤ J → Nat.card A = 4 → (∀ x ∈ A, x ^ 2 = 1) →
      ∀ D : Finset (Fin n), (∀ x : J, (x : X) ∈ A → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) →
      IsPGroup 2 (A.subgroupOf J) ∧ Nat.card ((A.subgroupOf J).map π) = 4 ∧
        (∀ a ∈ (A.subgroupOf J).map π, a ^ 2 = 1) ∧
        ∀ a ∈ (A.subgroupOf J).map π, ∀ ω ∉ D, (a : Equiv.Perm (Fin n)) ω = ω := by
    intro A hAJ hA4 hA2 D hAs
    have hcardA : Nat.card (A.subgroupOf J) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv, hA4]
    have hp : IsPGroup 2 (A.subgroupOf J) := IsPGroup.of_card (n := 2) (by rw [hcardA]; norm_num)
    refine ⟨hp, ?_, ?_, ?_⟩
    · rw [card_map_of_inf_ker π _ (inf_eq_bot_of_two_odd hp hO), hcardA]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA2 _ hx)
      rw [this, map_one]
    · rintro _ ⟨x, hx, rfl⟩ ω hω
      exact hAs x hx ω hω
  obtain ⟨hpE, hE4, hEsq, hEsupp⟩ := himg E hEJ hE hE2 DE hEs
  obtain ⟨hpF, hF4, hFsq, hFsupp⟩ := himg F hFJ hF hF2 DF hFs
  have hgen := Sol78.normalizer_sup_normalizer_eq_top hn hE4 hF4 hEsq hFsq hDE hDF hdisj
    hEsupp hFsupp
  have htop := normalizer_sup_normalizer_sup_odd_eq_top π hπ hO hpE hpF hgen
  rw [hker] at htop
  intro x hx
  have hx' : (⟨x, hx⟩ : J) ∈ (normalizer ((E.subgroupOf J : Subgroup J) : Set J) ⊔
      normalizer ((F.subgroupOf J : Subgroup J) : Set J) ⊔ pPrimeCore 2 J) := htop ▸ mem_top _
  have hmap := mem_map_of_mem J.subtype hx'
  rw [Subgroup.map_sup, Subgroup.map_sup] at hmap
  exact (sup_le_sup (sup_le_sup (map_normalizer_subgroupOf_le hEJ)
    (map_normalizer_subgroupOf_le hFJ)) le_rfl) hmap

@[expose] noncomputable def kleinOn {n : ℕ} (D : Finset (Fin n)) (hD : D.card = 4) :
    Subgroup (alternatingGroup (Fin n)) :=
  (altFourKlein.map ((Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hD] :
    Fintype.card ↥D = 4)).altCongrHom.symm.toMonoidHom)).map (alternatingGroup.ofSubtype D)

theorem card_kleinOn {n : ℕ} (D : Finset (Fin n)) (hD : D.card = 4) :
    Nat.card (kleinOn D hD) = 4 := by
  unfold kleinOn
  rw [Subgroup.card_map_of_injective alternatingGroup.ofSubtype_injective,
    Subgroup.card_map_of_injective (MulEquiv.injective _), card_altFourKlein]

theorem sq_kleinOn {n : ℕ} {D : Finset (Fin n)} {hD : D.card = 4} :
    ∀ σ ∈ kleinOn D hD, σ * σ = 1 := by
  rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
  have hτ' : τ * τ = 1 := hτ
  rw [← map_mul, ← map_mul, hτ', map_one, map_one]

theorem support_kleinOn {n : ℕ} {D : Finset (Fin n)} {hD : D.card = 4} :
    ∀ σ ∈ kleinOn D hD, ∀ ω ∉ D, (σ : Equiv.Perm (Fin n)) ω = ω := by
  classical
  rintro _ ⟨τ, -, rfl⟩ ω hω
  have h1 := (alternatingGroup.mem_range_ofSubtype_iff D (alternatingGroup.ofSubtype D τ)).mp
    ⟨τ, rfl⟩
  by_contra hc
  exact hω (h1 (Equiv.Perm.mem_support.mpr hc))

theorem commute_of_support {n : ℕ} {D D' : Finset (Fin n)} (hdisj : Disjoint D D')
    {σ τ : Equiv.Perm (Fin n)} (hσ : ∀ ω ∉ D, σ ω = ω) (hτ : ∀ ω ∉ D', τ ω = ω) :
    σ * τ = τ * σ := by
  have hd : σ.Disjoint τ := by
    intro ω
    by_cases hωD : ω ∈ D
    · exact Or.inr (hτ ω (Finset.disjoint_left.mp hdisj hωD))
    · exact Or.inl (hσ ω hωD)
  exact hd.commute.eq

theorem exists_lift_two_subgroup' {G Q : Type*} [Group G] [Group Q] [Finite G] (f : G →* Q)
    (hker : Odd (Nat.card f.ker)) (V : Subgroup Q) (hV : IsPGroup 2 V) (hVr : V ≤ f.range) :
    ∃ P : Subgroup G, P.map f = V ∧ ∀ x ∈ P, f x = 1 → x = 1 := by
  have hk : f.rangeRestrict.ker = f.ker := MonoidHom.ker_rangeRestrict f
  have hV' : IsPGroup 2 (V.subgroupOf f.range) :=
    hV.of_equiv (subgroupOfEquivOfLe hVr).symm
  obtain ⟨P, hPV, hPinj⟩ := exists_lift_two_subgroup f.rangeRestrict f.rangeRestrict_surjective
    (hk ▸ hker) (V.subgroupOf f.range) hV'
  refine ⟨P, ?_, fun x hx hx1 => hPinj x hx (Subtype.ext hx1)⟩
  have h1 := congrArg (fun A : Subgroup f.range => A.map f.range.subtype) hPV
  simp only [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hVr] at h1
  rw [← h1]
  rfl

theorem exists_commuting_four_subgroup {X : Type} [Group X] [Finite X] {J : Subgroup X} {n : ℕ}
    (hn : 9 ≤ n) (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {E : Subgroup X}
    (hEJ : E ≤ J) (hE2 : IsPGroup 2 E) {D : Finset (Fin n)} (hD : D.card = 4)
    (hDs : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) :
    ∃ (F : Subgroup X) (D' : Finset (Fin n)), F ≤ J ∧ Nat.card F = 4 ∧
      (∀ x ∈ F, x * x = 1) ∧ D'.card = 4 ∧ Disjoint D D' ∧
      (∀ x : J, (x : X) ∈ F → ∀ ω ∉ D',
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω) ∧
      F ≤ centralizer (E : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D', hD'sub, hD'⟩ := Finset.exists_subset_card_eq (s := Dᶜ) (n := 4)
    (by rw [Finset.card_compl, Fintype.card_fin, hD]; omega)
  have hdisj : Disjoint D D' := by
    rw [Finset.disjoint_right]
    intro ω hω
    exact Finset.mem_compl.mp (hD'sub hω)
  set V := kleinOn D' hD' with hVdef
  have hV4 : Nat.card V = 4 := card_kleinOn D' hD'
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  let π : J →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 J))
  have hker : π.ker = pPrimeCore 2 J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (pPrimeCore 2 J) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set E' := E.subgroupOf J with hE'def
  set C := centralizer (E' : Set J) with hCdef
  let πC : C →* alternatingGroup (Fin n) := π.comp C.subtype
  have hkerC : Odd (Nat.card πC.ker) := by
    have h1 : Nat.card πC.ker ∣ Nat.card (pPrimeCore 2 J) := by
      have hle : (πC.ker).map C.subtype ≤ pPrimeCore 2 J := by
        rintro _ ⟨c, hc, rfl⟩
        rw [← hker]
        exact hc
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  have hVr : V ≤ πC.range := by
    intro v hv
    set α : E' →* MulAut J := MulAut.conj.comp E'.subtype with hαdef
    have hN : ∀ a : E', ∀ m ∈ pPrimeCore 2 J, α a m ∈ pPrimeCore 2 J := fun a m hm =>
      (inferInstance : (pPrimeCore 2 J).Normal).conj_mem m hm a
    have hcop : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) := fun h =>
      (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
        (even_iff_two_dvd.mpr h)
    have hE'2 : IsPGroup 2 E' := hE2.of_equiv (subgroupOfEquivOfLe hEJ).symm
    have hfix := Semidihedral.Principal.coprime_fixed_point_lifting 2 hE'2 α (pPrimeCore 2 J) hN
      hcop
    have hq : e.symm v ∈ {q : J ⧸ pPrimeCore 2 J | ∀ a : E',
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (pPrimeCore 2 J) hN a q = q} := by
      intro a
      obtain ⟨j, hj⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 J) (e.symm v)
      rw [← hj]
      change QuotientGroup.mk' (pPrimeCore 2 J) ((a : J) * j * (a : J)⁻¹) =
        QuotientGroup.mk' (pPrimeCore 2 J) j
      apply e.injective
      have hav : (e (QuotientGroup.mk' (pPrimeCore 2 J) (a : J)) : Equiv.Perm (Fin n)) *
          (v : Equiv.Perm (Fin n)) = (v : Equiv.Perm (Fin n)) *
          (e (QuotientGroup.mk' (pPrimeCore 2 J) (a : J)) : Equiv.Perm (Fin n)) :=
        commute_of_support hdisj (hDs (a : J) a.2) (support_kleinOn v hv)
      have hjv : e (QuotientGroup.mk' (pPrimeCore 2 J) j) = v := by
        rw [hj, MulEquiv.apply_symm_apply]
      rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hjv]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hav]
      group
    rw [hfix] at hq
    obtain ⟨c, hc, hcq⟩ := hq
    have hcC : c ∈ C := by
      rw [hCdef, mem_centralizer_iff]
      intro a ha
      have h1 : α ⟨a, ha⟩ c = c := hc ⟨a, ha⟩
      have h2 : a * c * a⁻¹ = c := h1
      calc a * c = a * c * a⁻¹ * a := by group
        _ = c * a := by rw [h2]
    refine ⟨⟨c, hcC⟩, ?_⟩
    change e (QuotientGroup.mk' (pPrimeCore 2 J) c) = v
    rw [hcq, MulEquiv.apply_symm_apply]
  obtain ⟨P, hPV, hPinj⟩ := exists_lift_two_subgroup' πC hkerC V hV2 hVr
  have hPcard : Nat.card P = 4 := by
    have h1 : Function.Injective (πC.comp P.subtype) := by
      intro a b hab
      have hab' : πC ((a : C) * (b : C)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        exact mul_inv_eq_one.mpr hab
      exact Subtype.ext (mul_inv_eq_one.mp (hPinj _ (mul_mem a.2 (inv_mem b.2)) hab'))
    have h2 : (πC.comp P.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPV]
    rw [← hV4, ← h2]
    exact Nat.card_congr (MonoidHom.ofInjective h1).toEquiv
  set F := (P.map C.subtype).map J.subtype with hFdef
  have hmemF : ∀ x : J, (x : X) ∈ F → ∃ c ∈ P, (c : J) = x := by
    rintro x ⟨_, ⟨c, hc, rfl⟩, hcx⟩
    exact ⟨c, hc, Subtype.ext hcx⟩
  refine ⟨F, D', ?_, ?_, ?_, hD', hdisj, ?_, ?_⟩
  · exact map_subtype_le _
  · rw [hFdef, Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective, hPcard]
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have hfc : πC c ∈ V := hPV ▸ mem_map_of_mem πC hc
    have h1 : πC (c * c) = 1 := by rw [map_mul, sq_kleinOn _ hfc]
    have := hPinj _ (mul_mem hc hc) h1
    change (((c * c : C) : J) : X) = 1
    rw [this]
    rfl
  · intro x hx ω hω
    obtain ⟨c, hc, rfl⟩ := hmemF x hx
    have hfc : πC c ∈ V := hPV ▸ mem_map_of_mem πC hc
    exact support_kleinOn _ hfc ω hω
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro a ha
    have hcC : (c : J) ∈ centralizer (E' : Set J) := c.2
    rw [mem_centralizer_iff] at hcC
    have := hcC ⟨a, hEJ ha⟩ ha
    exact congrArg Subtype.val this

end CFSG.ComponentClassification.SolMax
