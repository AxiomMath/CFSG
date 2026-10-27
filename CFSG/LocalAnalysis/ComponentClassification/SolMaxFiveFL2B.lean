module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallH
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent

public section

namespace CFSG.ComponentClassification.SolMax.FiveFL2

open CFSG Subgroup Equiv CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open CatalogueSchreierLinearTwo (semilinearAction semilinearAction_inl semilinearAction_inr
  semilinearEquivAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem le_coreActionKernel_of_fixed_pPrimeCore [Finite X] {M X₀ : Subgroup X} {c s : X}
    (hMC : M ≤ centralizer ({c} : Set X)) (hsN : s ∈ normalizer (M : Set X)) (hs2 : s * s = 1)
    (hinner : ∀ φ : MulAut (↥M ⧸ pPrimeCore 2 ↥M), Odd (orderOf φ) → ∃ g, φ = MulAut.conj g)
    (hconj_inj : Function.Injective
      (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M)))
    (hO : pPrimeCore 2 (fixedSubgroup (TBLit.oddQuotAction M ⟨s, hsN⟩)) = ⊥)
    (hodd : Odd (Nat.card X₀)) (hX₀N : X₀ ≤ normalizer (M : Set X))
    (hX₀s : X₀ ≤ centralizer ({s} : Set X))
    (hX₀n : ∀ g ∈ centralizer ({s} : Set X) ⊓ centralizer ({c} : Set X), ∀ x ∈ X₀,
      g * x * g⁻¹ ∈ X₀) :
    X₀ ≤ UnbalancedLayer.coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := TBLit.oddQuotAction M with hAdef
  set sb := A ⟨s, hsN⟩ with hsbdef
  have hAM : ∀ (x : X) (hx : x ∈ M), A ⟨x, le_normalizer hx⟩ =
      MulAut.conj ((⟨x, hx⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
    intro x hx
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hAdef, TBLit.oddQuotAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
  have hcakA : ∀ (g : X) (hg : g ∈ normalizer (M : Set X)), A ⟨g, hg⟩ = 1 →
      g ∈ UnbalancedLayer.coreActionKernel M :=
    fun g hg h => (mem_coreActionKernel_iff_oddQuotAction hg).mpr h
  set P : Subgroup (MulAut (↥M ⧸ pPrimeCore 2 ↥M)) :=
    (X₀.subgroupOf (normalizer (M : Set X))).map A with hPdef
  set Q : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) := P.comap MulAut.conj with hQdef
  have hPodd : Odd (Nat.card P) := by
    have h1 : Nat.card P ∣ Nat.card (X₀.subgroupOf (normalizer (M : Set X))) :=
      card_map_dvd _ _
    rw [Nat.card_congr (subgroupOfEquivOfLe hX₀N).toEquiv] at h1
    exact hodd.of_dvd_nat h1
  have hQodd : Odd (Nat.card Q) := by
    let f : Q →* P := ((MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut _).comp
      Q.subtype).codRestrict P fun q => q.2
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (hconj_inj (congrArg Subtype.val h))
    exact hPodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  have hPinner : ∀ (x : X) (hx : x ∈ X₀), ∃ q ∈ Q, A ⟨x, hX₀N hx⟩ = MulAut.conj q := by
    intro x hx
    have hxodd : Odd (orderOf (A ⟨x, hX₀N hx⟩)) := by
      have h1 : orderOf (A ⟨x, hX₀N hx⟩) ∣
          orderOf (⟨x, hX₀N hx⟩ : ↥(normalizer (M : Set X))) := orderOf_map_dvd A _
      rw [Subgroup.orderOf_mk] at h1
      have h2 : orderOf x ∣ Nat.card X₀ := by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : X₀)
        rwa [Subgroup.orderOf_mk] at this
      exact (hodd.of_dvd_nat h2).of_dvd_nat h1
    obtain ⟨q, hq⟩ := hinner _ hxodd
    refine ⟨q, ?_, hq⟩
    change MulAut.conj q ∈ P
    rw [← hq]
    exact ⟨⟨x, hX₀N hx⟩, hx, rfl⟩
  have hQF : ∀ q ∈ Q, sb q = q := by
    intro q hq
    obtain ⟨⟨x, hxN⟩, hx, hxq⟩ := hq
    have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp (hX₀s hx)
    have h1 : A ⟨x, hxN⟩ * sb = sb * A ⟨x, hxN⟩ := by
      rw [hsbdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxs
    rw [hxq] at h1
    have h3 : MulAut.conj (sb q) = sb * MulAut.conj q * sb⁻¹ := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    have h4 : sb * MulAut.conj q * sb⁻¹ = MulAut.conj q := by
      rw [← h1, mul_inv_cancel_right]
    exact hconj_inj (h3.trans h4)
  have hQn : ∀ cb : ↥M ⧸ pPrimeCore 2 ↥M, sb cb = cb → ∀ q ∈ Q, cb * q * cb⁻¹ ∈ Q := by
    intro cb hcb q hq
    obtain ⟨⟨x, hxN⟩, hx, hxq⟩ := hq
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective cb
    have hc₀s : (c₀ : X)⁻¹ * (s * c₀ * s⁻¹) ∈ coreNOf M := by
      have h1 : A ⟨s, hsN⟩ (c₀ : ↥M ⧸ pPrimeCore 2 ↥M) = (c₀ : ↥M ⧸ pPrimeCore 2 ↥M) := hcb
      rw [hAdef, TBLit.oddQuotAction_mk] at h1
      have h2 := QuotientGroup.eq.mp h1.symm
      exact ⟨_, h2, rfl⟩
    obtain ⟨k, hkO, hkc⟩ := exists_commute_of_mem_coset (odd_coreNOf M) hs2
      (fun o ho => (mem_normalizer_iff.mp (le_normalizer_pPrimeCore hsN) o).mp ho) hc₀s
    obtain ⟨k', hk', hk'eq⟩ := hkO
    have hkM : k ∈ M := by rw [← hk'eq]; exact k'.2
    have hc'M : (c₀ : X) * k ∈ M := mul_mem c₀.2 hkM
    have hc'b : ((⟨(c₀ : X) * k, hc'M⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        (c₀ : ↥M ⧸ pPrimeCore 2 ↥M) := by
      have h1 : (⟨(c₀ : X) * k, hc'M⟩ : ↥M) = c₀ * k' :=
        Subtype.ext (by change (c₀ : X) * k = (c₀ : X) * (k' : X); rw [← hk'eq]; rfl)
      rw [h1, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k').mpr hk', mul_one]
    have hc's : (c₀ : X) * k ∈ centralizer ({s} : Set X) :=
      mem_centralizer_singleton_iff.mpr hkc.symm
    have hc'c : (c₀ : X) * k ∈ centralizer ({c} : Set X) := hMC hc'M
    have hx' : ((c₀ : X) * k) * x * ((c₀ : X) * k)⁻¹ ∈ X₀ := hX₀n _ ⟨hc's, hc'c⟩ x hx
    refine ⟨⟨((c₀ : X) * k) * x * ((c₀ : X) * k)⁻¹, hX₀N hx'⟩, hx', ?_⟩
    have hc'N : (c₀ : X) * k ∈ normalizer (M : Set X) := le_normalizer hc'M
    have h3 : (⟨((c₀ : X) * k) * x * ((c₀ : X) * k)⁻¹, hX₀N hx'⟩ :
        ↥(normalizer (M : Set X))) = ⟨(c₀ : X) * k, hc'N⟩ * ⟨x, hxN⟩ * ⟨(c₀ : X) * k, hc'N⟩⁻¹ :=
      rfl
    rw [h3, map_mul, map_mul, map_inv, hxq, hAM _ hc'M, hc'b, ← map_inv, ← map_mul, ← map_mul]
  have hQbot : Q = ⊥ := by
    have hQle : Q ≤ fixedSubgroup sb := fun q hq => hQF q hq
    set W := Q.subgroupOf (fixedSubgroup sb) with hWdef
    have hWn : W.Normal := ⟨fun w hw h => by
      rw [hWdef, mem_subgroupOf] at hw ⊢
      exact hQn h h.2 w hw⟩
    have hWodd : Nat.Coprime 2 (Nat.card W) := by
      rw [hWdef, Nat.card_congr (subgroupOfEquivOfLe hQle).toEquiv]
      exact Nat.coprime_two_left.mpr hQodd
    have hWle : W ≤ pPrimeCore 2 (fixedSubgroup sb) := le_sSup ⟨hWn, hWodd⟩
    rw [hO, le_bot_iff, hWdef, subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hQle] at hWle
    exact hWle
  intro x hx
  obtain ⟨q, hq, hxq⟩ := hPinner x hx
  rw [hQbot, mem_bot] at hq
  refine hcakA x (hX₀N hx) ?_
  rw [hxq, hq, map_one]

variable {F : Type} [Field F] [Finite F] {Y : Type} [Group Y]

theorem exists_eq_conj_of_odd_psl2_sq {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ 2)
    (e : Y ≃* PSL2 F) (φ : MulAut Y) (hφ : Odd (orderOf φ)) : ∃ y : Y, φ = MulAut.conj y := by
  set g := autEquiv e φ with hgdef
  have hgo : orderOf g = orderOf φ := MulEquiv.orderOf_eq _ φ
  have hr : g.right = 1 := by
    have h1 : orderOf g.right ∣ orderOf g :=
      orderOf_map_dvd (SemidirectProduct.rightHom) g
    have h2 : orderOf g.right ∣ Nat.card (F ≃+* F) := orderOf_dvd_natCard _
    rw [card_ringAut F hp hF] at h2
    rw [hgo] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h1
      exact absurd (hφ.of_dvd_nat h1) (by decide)
  have hgl : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hr
  have hxo : Odd (orderOf g.left) := by
    have h1 : orderOf g.left = orderOf g := by
      conv_rhs => rw [hgl]
      exact (orderOf_injective _ SemidirectProduct.inl_injective g.left).symm
    rw [h1, hgo]
    exact hφ
  obtain ⟨k, hk⟩ := hxo
  have hx : g.left = (g.left ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g.left + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hxr : g.left ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rw [hx]
    exact pow_mem (sq_mem_psl2Range _) _
  obtain ⟨z, hz⟩ := hxr
  refine ⟨e.symm z, (autEquiv e).injective ?_⟩
  rw [autEquiv_conj, MulEquiv.apply_symm_apply, incl_apply, hz, ← hgl]

theorem conj_injective_psl2 (e : Y ≃* PSL2 F) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hgZ : e g ∈ center (PSL2 F) := by
    rw [mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut Y => φ (e.symm h)) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    have h2 := congrArg e h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    calc h * e g = e g * h * (e g)⁻¹ * e g := by rw [h2]
      _ = e g * h := by group
  rw [psl2_center_eq_bot, mem_bot] at hgZ
  exact mem_bot.mpr (e.injective (by rw [hgZ, map_one]))

theorem pPrimeCore_eq_bot_psl2 (hpp : IsOddPrimePower (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (e : Y ≃* PSL2 F) : pPrimeCore 2 Y = ⊥ := by
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : IsSimpleGroup Y := e.isSimpleGroup
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 Y) with h | h
  · exact h
  · exfalso
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 Y)) := pPrimeCore_coprime_card
    rw [h, card_top, Nat.card_congr e.toEquiv] at hcop
    have hev := even_psl2_card hpp
    rw [Nat.coprime_two_left] at hcop
    exact (Nat.not_even_iff_odd.mpr hcop) hev

theorem map_fixedSubgroup_mulAutConj {G : Type*} [Group G] (c φ : MulAut G) :
    (fixedSubgroup φ).map c.toMonoidHom = fixedSubgroup (c * φ * c⁻¹) := by
  ext y
  rw [mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change c (φ (c⁻¹ (c x))) = c x
    rw [MulAut.inv_apply_self]
    exact congrArg c (show φ x = x from hx)
  · intro hy
    have h1 : c (φ (c⁻¹ y)) = y := hy
    refine ⟨c⁻¹ y, ?_, by simp⟩
    change φ (c⁻¹ y) = c⁻¹ y
    calc φ (c⁻¹ y) = c⁻¹ (c (φ (c⁻¹ y))) := by simp
      _ = c⁻¹ y := by rw [h1]

theorem pPrimeCore_fixedSubgroup_field
    (hpp : IsOddPrimePower (Nat.card F)) (α : MulAut (PSL2 F)) (hα2 : α * α = 1)
    (hr : ((semilinearEquivAut F).symm α).right ≠ 1) : pPrimeCore 2 (fixedSubgroup α) = ⊥ := by
  classical
  set g := (semilinearEquivAut F).symm α with hgdef
  have hgα : semilinearAction F g = α := (semilinearEquivAut F).apply_symm_apply α
  have hgg : g * g = 1 := by rw [hgdef, ← map_mul, hα2, map_one]
  have hg1 : g ≠ 1 := fun h => hr (by rw [h]; rfl)
  have hgo : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hgg) hg1
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hpp g hgo hr
  have hσσ' : g.right * g.right = 1 := by
    have := congrArg SemidirectProduct.right hgg
    simpa using this
  have hσ : orderOf g.right = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ') hr
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield g.right hσ
  have hσσ : ∀ x, g.right (g.right x) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hσσ'
    simpa using this
  set c : MulAut (PSL2 F) := semilinearAction F (SemidirectProduct.inl C) with hc
  have hgC : g = SemidirectProduct.inl C * SemidirectProduct.inr g.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have hαc : α = c * psl2FieldAut F g.right * c⁻¹ := by
    rw [← hgα, hc]
    conv_lhs => rw [hgC]
    rw [map_mul, map_mul, map_inv, semilinearAction_inr]
  have hO : pPrimeCore 2 (fieldCent g.right) = ⊥ := by
    set N := (pPrimeCore 2 (fieldCent g.right)).map (fieldCent g.right).subtype with hNdef
    have hNC : N ≤ fieldCent g.right := map_subtype_le _
    have hNn : ∀ c' ∈ fieldCent g.right, ∀ n ∈ N, c' * n * c'⁻¹ ∈ N := by
      rintro c' hc' _ ⟨n, hn, rfl⟩
      exact ⟨⟨c', hc'⟩ * n * ⟨c', hc'⟩⁻¹,
        (pPrimeCore_normal (p := 2) (G := fieldCent g.right)).conj_mem n hn _, rfl⟩
    have hNodd : Odd (Nat.card N) := by
      rw [hNdef, card_map_of_injective (fieldCent g.right).subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h1 := eq_bot_of_odd_normal_fieldCent hK₀ h90 hσσ hcard hpp hNC hNn hNodd
    rw [hNdef, map_eq_bot_iff_of_injective _ (fieldCent g.right).subtype_injective] at h1
    exact h1
  have hfix : (fieldCent g.right).map c.toMonoidHom = fixedSubgroup α := by
    rw [hαc]
    exact map_fixedSubgroup_mulAutConj c (psl2FieldAut F g.right)
  let ec : fieldCent g.right ≃* fixedSubgroup α :=
    ((fieldCent g.right).equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr hfix)
  rw [← pPrimeCore_map_iso 2 ec, hO, Subgroup.map_bot]

end CFSG.ComponentClassification.SolMax.FiveFL2
