module

public import CFSG.CGT.Foote81L6.Normalizer.Conjugacy
public import CFSG.CGT.Foote81L6.Normalizer.SmallPGL
public import CFSG.CGT.Foote81L6.Normalizer.SymBasic
public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.Quasithin.Recognition.M12AscTrans

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin CFSG.GorensteinWalter Equiv

@[expose] def HigmanHyp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {a : G}, orderOf a = 2 → a ∈ S →
    Subgroup.normalClosure ({a} : Set G) = ⊤ → {x | x ∈ S ∧ IsConj a x}.ncard = 2 →
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) ∧
      Nonempty (G ⧸ pPrimeCore 2 G ≃* PGL2 K)

private theorem prod_gl_six : ∏ i : Fin 6, (2 ^ 6 - 2 ^ (i : ℕ)) = 20158709760 := by
  simp [Fin.prod_univ_six]

namespace TvHyp

variable {V X : Type} [CommGroup V] [Finite V] [Group X] [Finite X] {ρ : X →* MulAut V}
  {D : Sylow 2 X} {d₀ d₁ : X}

theorem card_dvd (h : TvHyp ρ D d₀ d₁) : Nat.card X ∣ 20158709760 := by
  have h1 : Nat.card X = Nat.card ρ.range :=
    Nat.card_congr (MonoidHom.ofInjective h.injective).toEquiv
  rw [h1, ← prod_gl_six, ← MulAutTwo.card_mulAut h.sq_eq_one h.card_eq]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_sylow (h : TvHyp ρ D d₀ d₁) : Nat.card (D : Subgroup X) = 8 := by
  obtain ⟨ψ⟩ := h.dihedral
  rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]

theorem not_dvd_card (h : TvHyp ρ D d₀ d₁) : ¬ 16 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h16
  have hidx := D.not_dvd_index
  have hX := (D : Subgroup X).card_mul_index
  rw [h.card_sylow] at hX
  rw [← hX] at h16
  exact hidx (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8)
    (by rw [show (8 : ℕ) * 2 = 16 by norm_num]; exact h16))

theorem exists_quotient_mulEquiv (h : TvHyp ρ D d₀ d₁) (hnc : ¬ HasNormalPComplement 2 X)
    (hHig : HigmanHyp) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty (X ⧸ pPrimeCore 2 X ≃* Perm (Fin n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X₀ := Subgroup.normalClosure ({d₀} : Set X) with hX₀
  have hd₀X₀ : d₀ ∈ X₀ := Subgroup.subset_normalClosure rfl
  have hisoX₀ : ∀ t : X, IsConj d₀ t → t ∈ X₀ := fun t ht =>
    Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.mem_conjugatesOfSet_iff.mpr ⟨d₀, rfl, ht⟩)
  have hd₁X₀ : d₁ ∈ X₀ := hisoX₀ d₁ h.isConj₁
  obtain ⟨x₁, hx₁, hx₁d⟩ := h.exists_conj_mem_normalClosure hnc
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq X₀ D
  have hPD : ∀ s : X₀, s ∈ (P : Subgroup X₀) ↔ (s : X) ∈ (D : Subgroup X) := by
    intro s
    rw [hP]
    rfl
  have hcls₀ : ∀ t : X, IsConj d₀ t → ∃ y ∈ X₀, y * d₀ * y⁻¹ = t := by
    intro t ht
    have htX₀ := hisoX₀ t ht
    have ht2 : t * t = 1 := by
      obtain ⟨c, rfl⟩ := isConj_iff.mp ht
      calc c * d₀ * c⁻¹ * (c * d₀ * c⁻¹) = c * (d₀ * d₀) * c⁻¹ := by group
        _ = 1 := by rw [h.sq₀, mul_one, mul_inv_cancel]
    obtain ⟨x, hx⟩ := exists_conj_mem_sylow_two P (t := ⟨t, htX₀⟩) (Subtype.ext ht2)
    have hxD : (x : X) * t * (x : X)⁻¹ ∈ (D : Subgroup X) := (hPD _).mp hx
    rcases (h.fusion _ hxD).mp (ht.trans (isConj_iff.mpr ⟨x, rfl⟩)) with h1 | h1
    · refine ⟨(x : X)⁻¹, X₀.inv_mem x.2, ?_⟩
      rw [← h1]
      group
    · refine ⟨(x : X)⁻¹ * x₁, X₀.mul_mem (X₀.inv_mem x.2) hx₁, ?_⟩
      calc (x : X)⁻¹ * x₁ * d₀ * ((x : X)⁻¹ * x₁)⁻¹
          = (x : X)⁻¹ * (x₁ * d₀ * x₁⁻¹) * x := by group
        _ = t := by rw [hx₁d, ← h1]; group
  set a : X₀ := ⟨d₀, hd₀X₀⟩ with ha
  have hord : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.sq₀) h.ne_one₀
  have haP : a ∈ P := (hPD a).mpr h.mem₀
  have hgen : Subgroup.normalClosure ({a} : Set X₀) = ⊤ := by
    have hle : X₀ ≤ (Subgroup.normalClosure ({a} : Set X₀)).map X₀.subtype := by
      change Subgroup.closure (Group.conjugatesOfSet ({d₀} : Set X)) ≤ _
      rw [Subgroup.closure_le]
      intro t ht
      obtain ⟨b, hb, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp ht
      rw [Set.mem_singleton_iff] at hb
      rw [hb] at hconj
      obtain ⟨y, hy, rfl⟩ := hcls₀ t hconj
      refine ⟨⟨y, hy⟩ * a * ⟨y, hy⟩⁻¹, ?_, rfl⟩
      exact Subgroup.conjugatesOfSet_subset_normalClosure
        (Group.mem_conjugatesOfSet_iff.mpr ⟨a, rfl, isConj_iff.mpr ⟨⟨y, hy⟩, rfl⟩⟩)
    rw [eq_top_iff]
    intro g _
    obtain ⟨m, hm, hmg⟩ := hle g.2
    have : m = g := Subtype.ext hmg
    rw [← this]
    exact hm
  set b : X₀ := ⟨d₁, hd₁X₀⟩ with hb
  have hab : a ≠ b := fun h1 => h.ne (congrArg Subtype.val h1)
  have hncard : {x | x ∈ P ∧ IsConj a x}.ncard = 2 := by
    have hset : {x | x ∈ P ∧ IsConj a x} = {a, b} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxP, hconj⟩
        obtain ⟨c, hc⟩ := isConj_iff.mp hconj
        have hc' : (c : X) * d₀ * (c : X)⁻¹ = x := by
          rw [← hc]
          rfl
        rcases (h.fusion _ ((hPD x).mp hxP)).mp (isConj_iff.mpr ⟨c, hc'⟩) with h1 | h1
        · exact Or.inl (Subtype.ext h1)
        · exact Or.inr (Subtype.ext h1)
      · rintro (rfl | rfl)
        · exact ⟨haP, IsConj.refl _⟩
        · refine ⟨(hPD _).mpr h.mem₁, isConj_iff.mpr ⟨⟨x₁, hx₁⟩, Subtype.ext ?_⟩⟩
          exact hx₁d
    rw [hset, Set.ncard_pair hab]
  obtain ⟨K, instK, instKf, hmod, ⟨e⟩⟩ := hHig P hord haP hgen hncard
  have hLdvd : Nat.card K * (Nat.card K ^ 2 - 1) ∣ Nat.card X := by
    rw [← pgl2_card_formula, ← Nat.card_congr e.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card X₀)
  obtain ⟨p, k, hp, hk⟩ : ∃ p k : ℕ, p.Prime ∧ Nat.card K = p ^ k := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨p, hchar, k, hp, hk⟩ := FiniteField.card' K
    exact ⟨p, k, hp, by rw [Nat.card_eq_fintype_card, hk]⟩
  have hq : Nat.card K = 3 ∨ Nat.card K = 5 := by
    rw [hk] at hmod hLdvd ⊢
    exact eq_three_or_five_of_dvd hp hmod (hLdvd.trans h.card_dvd)
  obtain ⟨n, hn, ⟨eS⟩⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (X₀ ⧸ pPrimeCore 2 X₀ ≃* Perm (Fin n)) := by
    rcases hq with hq | hq
    · exact ⟨4, Or.inl rfl, nonempty_mulEquiv_perm_four_of_pgl2 e hq⟩
    · exact ⟨5, Or.inr rfl, nonempty_mulEquiv_perm_five_of_pgl2 e hq⟩
  have h8 : 8 ∣ Nat.card X₀ := by
    have h1 : 8 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
      rcases hq with hq | hq <;> rw [hq] <;> norm_num
    rw [← pgl2_card_formula, ← Nat.card_congr e.toEquiv] at h1
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  have hZ : Subgroup.center (X₀ ⧸ pPrimeCore 2 X₀) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hec : e c ∈ Subgroup.center (PGL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
    rw [pgl2_center_eq_bot, Subgroup.mem_bot] at hec
    exact (Subgroup.mem_bot).mpr (e.injective (hec.trans (map_one e).symm))
  set O := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set f : X₀ →* X ⧸ O := π.comp X₀.subtype with hf
  have hker : f.ker = pPrimeCore 2 X₀ := by
    apply le_antisymm
    · refine le_sSup ⟨f.normal_ker, ?_⟩
      have hdvd : Nat.card f.ker ∣ Nat.card O := by
        rw [← Subgroup.card_map_of_injective X₀.subtype_injective]
        apply Subgroup.card_dvd_of_le
        rintro _ ⟨k, hk, rfl⟩
        have hk' : (QuotientGroup.mk (k : X) : X ⧸ O) = 1 := hk
        exact (QuotientGroup.eq_one_iff _).mp hk'
      exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    · intro k hk
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact map_pPrimeCore_le ⟨k, hk, rfl⟩
  have hrange : f.range = X₀.map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  set L : Subgroup (X ⧸ O) := X₀.map π with hL
  let θ : X₀ ⧸ pPrimeCore 2 X₀ ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  have hLn : L.Normal := Subgroup.Normal.map inferInstance π hπs
  have hLi : Odd L.index := by
    have hX₀i : Odd X₀.index := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2
      apply h.not_dvd_card
      rw [← X₀.card_mul_index]
      exact Nat.mul_dvd_mul h8 h2
    rw [hL, Subgroup.index_map, MonoidHom.range_eq_top.mpr hπs, Subgroup.index_top, mul_one]
    exact hX₀i.of_dvd_nat (Subgroup.index_dvd_of_le le_sup_left)
  have hZL : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hθc : θ.symm c ∈ Subgroup.center (X₀ ⧸ pPrimeCore 2 X₀) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := θ.symm.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc z]
    rw [hZ, Subgroup.mem_bot] at hθc
    exact (Subgroup.mem_bot).mpr (θ.symm.injective (hθc.trans (map_one θ.symm).symm))
  have hLtop : L = ⊤ := eq_top_of_normal_of_odd_index
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two) hLi hZL
    (exists_inner_of_mulEquiv_perm hn (θ.symm.trans eS))
  exact ⟨n, hn, ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans
    (θ.symm.trans eS)⟩⟩

theorem exists_normalized {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (h : TvHyp ρ D d₀ d₁)
    (φ : X ⧸ pPrimeCore 2 X ≃* Perm (Fin n)) :
    ∃ φ' : X ⧸ pPrimeCore 2 X ≃* Perm (Fin n), φ' (QuotientGroup.mk d₀) = swap 0 1 ∧
      φ' (QuotientGroup.mk d₁) = swap 2 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm01, -, -, -, -, ⟨c, hcD, hc⟩, -, ⟨Q, hQD, hQi, hd₀Q, hd₁Q⟩⟩ := h.dihedral_facts
  have hQu : ∀ g : X, g⁻¹ * d₀ * g ∉ Q := by
    intro g hg
    have hgD : g⁻¹ * d₀ * g⁻¹⁻¹ ∈ (D : Subgroup X) := by rw [inv_inv]; exact hQD hg
    rcases h.conj_eq hgD with h1 | h1
    · rw [inv_inv] at h1; rw [h1] at hg; exact hd₀Q hg
    · rw [inv_inv] at h1; rw [h1] at hg; exact hd₁Q hg
  obtain ⟨Y, -, hYi, hd₀Y, -⟩ := thompson_transfer_index_two D hQi h.sq₀ h.mem₀ hQu
  set O := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hOY : O ≤ Y := fun o ho => mem_of_index_two_of_odd_orderOf hYi
    (odd_orderOf_of_mem_pPrimeCore ho)
  have hYbar : ((Y.map π).map φ.toMonoidHom).index = 2 := by
    rw [Subgroup.index_map_of_injective _ φ.injective,
      MonoidHom.range_eq_top.mpr φ.surjective, Subgroup.index_top, mul_one, Subgroup.index_map,
      MonoidHom.range_eq_top.mpr hπs, Subgroup.index_top, mul_one, hπ, QuotientGroup.ker_mk',
      sup_eq_left.mpr hOY, hYi]
  have hA := Perm.alternatingGroup_le_of_index_le_two hYbar.le
  have hodd : ∀ d : X, IsConj d₀ d → Perm.sign (φ (π d)) = -1 := by
    intro d hd
    obtain ⟨g, rfl⟩ := isConj_iff.mp hd
    rcases Int.units_eq_one_or (Perm.sign (φ (π (g * d₀ * g⁻¹)))) with h1 | h1
    · exfalso
      have hmem := hA ((Perm.mem_alternatingGroup).mpr h1)
      obtain ⟨y, hy, hyd⟩ := hmem
      obtain ⟨y', hy', rfl⟩ := hy
      have h2 : π y' = π (g * d₀ * g⁻¹) := φ.injective hyd
      have h3 : y'⁻¹ * (g * d₀ * g⁻¹) ∈ O := QuotientGroup.eq.mp h2
      have h4 : g * d₀ * g⁻¹ ∈ Y := by
        have := Y.mul_mem hy' (hOY h3)
        simpa using this
      have h5 := (Subgroup.normal_of_index_eq_two hYi).conj_mem _ h4 g⁻¹
      apply hd₀Y
      simpa [mul_assoc] using h5
    · exact h1
  have hinv : ∀ d : X, d * d = 1 → φ (π d) * φ (π d) = 1 := fun d hd => by
    rw [← map_mul, ← map_mul, hd, map_one, map_one]
  obtain ⟨i, j, hij, hφ₀⟩ := perm_eq_swap_of_sign hn _ (hinv d₀ h.sq₀)
    (hodd d₀ (IsConj.refl d₀))
  obtain ⟨k, l, hkl, hφ₁⟩ := perm_eq_swap_of_sign hn _ (hinv d₁ h.sq₁) (hodd d₁ h.isConj₁)
  have hcomm : swap i j * swap k l = swap k l * swap i j := by
    rw [← hφ₀, ← hφ₁, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm01]
  have hne : swap i j ≠ swap k l := by
    rw [← hφ₀, ← hφ₁]
    intro h1
    exact h.ne (eq_of_mk_eq_of_mem_sylow D h.mem₀ h.mem₁ (φ.injective h1))
  obtain ⟨σ, hσ₀, hσ₁⟩ := perm_exists_conj_swap_pair hn i j k l hij hkl hcomm hne
  refine ⟨φ.trans (MulAut.conj σ), ?_, ?_⟩
  · show σ * φ (π d₀) * σ⁻¹ = swap 0 1
    rw [hφ₀, hσ₀]
  · show σ * φ (π d₁) * σ⁻¹ = swap 2 3
    rw [hφ₁, hσ₁]

end TvHyp

end CFSG.CGT.Foote81L6.Normalizer
