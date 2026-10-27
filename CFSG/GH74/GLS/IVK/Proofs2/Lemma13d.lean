module

public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma15a
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13dNC
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13dDih
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13dZig
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13dFY

public section

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.IVK.Proofs2

section Lemma13dMain

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem odd_mem_innAut (hF : L2Field F) (e : K ≃* L2 F) {g : MulAut K} (hg : g ∈ innDiagSub e)
    (hodd : Odd (orderOf g)) : g ∈ innAut K := by
  set H := innDiagSub e with hH
  set N : Subgroup ↥H := (innAut K).subgroupOf H with hN
  have hle : innAut K ≤ H := innAut_le_innDiagSub e
  have hcardN : Nat.card N = Nat.card K := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_L2 e)).toEquiv).symm
  have hidx : N.index = 2 := by
    have h1 : N.index * Nat.card N = Nat.card H := Subgroup.index_mul_card N
    rw [hcardN, card_innDiagSub e hF] at h1
    have : 0 < Nat.card K := Nat.card_pos
    nlinarith
  have hsq : (⟨g, hg⟩ : ↥H) ^ 2 ∈ N := Subgroup.sq_mem_of_index_two hidx _
  obtain ⟨m, hm⟩ := hodd
  have hpow : (⟨g, hg⟩ : ↥H) = ((⟨g, hg⟩ : ↥H) ^ 2) ^ (m + 1) := by
    have h1 : (⟨g, hg⟩ : ↥H) ^ orderOf (⟨g, hg⟩ : ↥H) = 1 := pow_orderOf_eq_one _
    have h2 : orderOf (⟨g, hg⟩ : ↥H) = orderOf g := Subgroup.orderOf_mk g hg
    rw [h2, hm] at h1
    rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, h1, one_mul]
  have : (⟨g, hg⟩ : ↥H) ∈ N := by
    rw [hpow]; exact N.pow_mem hsq _
  exact this

theorem exists_notation_containing (hF : L2Field F) (e : K ≃* L2 F) {u : MulAut K} (hu2 : orderOf u = 2) :
    ∃ e₁ : K ≃* L2 F, ∃ N : L2Notation e₁, u ∈ (N.T : Subgroup (MulAut K)) ∧
      innDiagSub e₁ = innDiagSub e := by
  have hp : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu2]; norm_num
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨e₁, N, hN⟩ := (ivk_1_2a F hF K e).1 S
  refine ⟨e₁, N, ?_, ?_⟩
  · rw [hN]; exact hS (Subgroup.mem_zpowers u)
  · let α : MulAut K := e₁.trans e.symm
    have : twistEquiv e α = e₁ := by
      ext k; simp [twistEquiv, α]
    rw [← this, innDiagSub_twist]

omit [Finite K] in
theorem centralizer_inndiag_dihedral (hF : L2Field F) (e : K ≃* L2 F) {u : MulAut K}
    (hu : u ∈ innDiagSub e) (hu2 : orderOf u = 2) :
    ∃ k : ℕ, 3 ≤ k ∧ (k = Nat.card F + 1 ∨ k + 1 = Nat.card F) ∧
      Nonempty (↥(centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e) ≃* DihedralGroup k) := by
  obtain ⟨A, rfl⟩ := hu
  have hpp := isOddPrimePower_of_L2Field hF
  have hq3 := hF.2
  obtain ⟨s5, hs5⟩ := hF.1
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    by_cases h : s5 % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  have hA2 : orderOf A = 2 := by
    rw [← orderOf_injective (innDiagHom e) (innDiagHom_injective e) A]
    exact hu2
  obtain ⟨hin, hout⟩ := pgl2_involution_centralizer_dihedral hpp hq3 hε1 hε hA2
  obtain ⟨ψ⟩ := centralizer_innDiag_equiv e A
  by_cases hAK : A ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  · obtain ⟨m, hm, ⟨φ⟩⟩ := hin hAK
    refine ⟨m, by omega, ?_, ⟨ψ.trans φ⟩⟩
    rcases hε1 with rfl | rfl
    · right; omega
    · left; omega
  · obtain ⟨m, hm, ⟨φ⟩⟩ := hout hAK
    refine ⟨m, by omega, ?_, ⟨ψ.trans φ⟩⟩
    rcases hε1 with rfl | rfl
    · left; omega
    · right; omega

theorem xuInn_eq_of_odd (hF : L2Field F) (e : K ≃* L2 F) {u : MulAut K}
    (X : Subgroup (MulAut K)) (hXD : X ≤ centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e)
    (hXnorm : ∀ d ∈ centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e, ∀ x ∈ X, d * x * d⁻¹ ∈ X)
    (hXodd_iff : ∀ g ∈ centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e, (Odd (orderOf g) ↔ g ∈ X))
    (hXodd : Odd (Nat.card X)) : xuInn u = X := by
  have hinj := conj_injective_of_L2 e
  have hconj_cent : ∀ k : K, MulAut.conj k ∈ centralizer ({u} : Set (MulAut K)) ↔ u k = k := by
    intro k
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := mul_conj_mul_inv_eq_conj_apply u k
    constructor
    · intro hc
      apply hinj
      rw [← h, ← hc]
      group
    · intro hk
      rw [hk] at h
      calc MulAut.conj k * u = (u * MulAut.conj k * u⁻¹) * u := by rw [h]
        _ = u * MulAut.conj k := by group
  have hconj_D : ∀ k : K, u k = k →
      MulAut.conj k ∈ centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e :=
    fun k hk => ⟨(hconj_cent k).mpr hk, innAut_le_innDiagSub e ⟨k, rfl⟩⟩
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨c, hc, rfl⟩ := hk
    have hcfix : u (c : K) = (c : K) := c.2
    have hD := hconj_D (c : K) hcfix
    have hodd : Odd (orderOf (MulAut.conj (c : K))) := by
      rw [orderOf_conj_eq e (c : K), Subgroup.orderOf_coe]
      exact Lemma118.odd_orderOf_pPrimeCore ⟨c, hc⟩
    exact (hXodd_iff _ hD).mp hodd
  · intro hx
    have hxD := hXD hx
    have hxodd := (hXodd_iff x hxD).mpr hx
    have hxinn : x ∈ innAut K := odd_mem_innAut hF e hxD.2 hxodd
    obtain ⟨k, rfl⟩ := hxinn
    set Q : Subgroup K := X.comap (MulAut.conj : K →* MulAut K) with hQ
    have hQfix : ∀ k' ∈ Q, u k' = k' := fun k' hk' => (hconj_cent k').mp (hXD hk').1
    have hXinn : X ≤ innAut K := fun y hy =>
      odd_mem_innAut hF e (hXD hy).2 ((hXodd_iff y (hXD hy)).mpr hy)
    have hQle : Q ≤ fixedSubgroup K u := fun k' hk' => hQfix k' hk'
    let Q' : Subgroup ↥(fixedSubgroup K u) := Q.subgroupOf (fixedSubgroup K u)
    have hQ'n : Q'.Normal := by
      refine ⟨fun n hn g => ?_⟩
      show MulAut.conj ((g : K) * (n : K) * (g : K)⁻¹) ∈ X
      have hn' : MulAut.conj (n : K) ∈ X := hn
      have hgD := hconj_D (g : K) g.2
      have := hXnorm _ hgD _ hn'
      simpa [map_mul, map_inv] using this
    have hQcard : Nat.card Q = Nat.card X := by
      have h1 : Q.map (MulAut.conj : K →* MulAut K) = X := by
        rw [hQ, Subgroup.map_comap_eq]
        exact inf_eq_right.mpr hXinn
      rw [← Subgroup.card_map_of_injective hinj, h1]
    have hQ'card : Odd (Nat.card Q') := by
      have : Nat.card Q' = Nat.card Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
      rw [this, hQcard]; exact hXodd
    have hQ'le : Q' ≤ pPrimeCore 2 ↥(fixedSubgroup K u) :=
      Lemma118.le_pPrimeCore_of_normal Q' hQ'card
    have hkQ : k ∈ Q := hx
    exact ⟨k, ⟨⟨k, hQfix k hkQ⟩, hQ'le (show (⟨k, hQfix k hkQ⟩ : ↥(fixedSubgroup K u)) ∈ Q' from hkQ),
      rfl⟩, rfl⟩


theorem exists_generator_centralizer (hF : L2Field F) (e : K ≃* L2 F) (u : MulAut K) :
    ∃ c₀ ∈ centralizer ({u} : Set (MulAut K)), ∀ c ∈ centralizer ({u} : Set (MulAut K)),
      ∃ d ∈ centralizer ({u} : Set (MulAut K)) ⊓ innDiagSub e, ∃ j : ℤ, c = d * c₀ ^ j := by
  obtain ⟨hcyc, ⟨ψ⟩, -⟩ := ivk_1_2e F hF K e
  have : IsCyclic ↥(fieldAutSub e) := hcyc
  have hcycF : IsCyclic (F ≃+* F) := isCyclic_of_surjective ψ.toMonoidHom ψ.surjective
  set C := centralizer ({u} : Set (MulAut K)) with hC
  have hcycC : IsCyclic ↥(C.map (fieldProj e)) := inferInstance
  obtain ⟨g₀, hg₀⟩ := hcycC.exists_generator
  obtain ⟨c₀, hc₀, hc₀g⟩ := g₀.2
  refine ⟨c₀, hc₀, fun c hc => ?_⟩
  have hπc : fieldProj e c ∈ C.map (fieldProj e) := ⟨c, hc, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨fieldProj e c, hπc⟩)
  have hj' : (g₀ : F ≃+* F) ^ j = fieldProj e c := by
    have := congrArg Subtype.val hj
    simpa using this
  refine ⟨c * c₀ ^ (-j), ?_, j, by group⟩
  refine ⟨mul_mem hc (zpow_mem hc₀ _), ?_⟩
  show c * c₀ ^ (-j) ∈ innDiagSub e
  rw [mem_innDiagSub_iff, map_mul, map_zpow, hc₀g, zpow_neg, hj']
  group

theorem exists_odd_fieldAut (hF : L2Field F) (e : K ≃* L2 F) :
    ∃ S : Subgroup (MulAut K), ∀ f, f ∈ S ↔ f ∈ fieldAutSub e ∧ Odd (orderOf f) := by
  obtain ⟨hcyc, -, -⟩ := ivk_1_2e F hF K e
  have : IsCyclic ↥(fieldAutSub e) := hcyc
  have hcomm : ∀ f ∈ fieldAutSub e, ∀ g ∈ fieldAutSub e, f * g = g * f := by
    intro f hf g hg
    have h := (IsCyclic.commGroup (α := ↥(fieldAutSub e))).mul_comm ⟨f, hf⟩ ⟨g, hg⟩
    exact congrArg Subtype.val h
  refine ⟨{ carrier := {f | f ∈ fieldAutSub e ∧ Odd (orderOf f)}
            one_mem' := ⟨one_mem _, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun f => Iff.rfl⟩
  · rintro f g ⟨hf, hfo⟩ ⟨hg, hgo⟩
    refine ⟨mul_mem hf hg, ?_⟩
    have h1 : orderOf (f * g) ∣ Nat.lcm (orderOf f) (orderOf g) :=
      Commute.orderOf_mul_dvd_lcm (hcomm f hf g hg)
    exact ((hfo.mul hgo).of_dvd_nat (Nat.lcm_dvd_mul _ _)).of_dvd_nat h1
  · rintro f ⟨hf, hfo⟩
    exact ⟨inv_mem hf, by simpa using hfo⟩

omit [Finite K] in
theorem exists_noncommuting_prime (hF : L2Field F) (e : K ≃* L2 F) {u : MulAut K}
    (X : Subgroup (MulAut K)) (hXu : xuInn u = X) {k : ℕ}
    (hkq : k = Nat.card F + 1 ∨ k + 1 = Nat.card F)
    (hXk : ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ k → s ∣ Nat.card X)
    {σ : MulAut K} (hσ : σ ∈ fieldAutSub e) {ℓ : ℕ} (hℓ : ℓ.Prime) (hσℓ : orderOf σ = ℓ)
    (hℓ2 : ℓ ≠ 2) :
    ∃ s : ℕ, s.Prime ∧ s ≠ ℓ ∧ s ∣ Nat.card X ∧ ∀ x ∈ X, orderOf x = s → σ * x ≠ x * σ := by
  obtain ⟨τ, rfl⟩ := hσ
  have hτ : orderOf τ = ℓ := by
    rw [← hσℓ]; exact (orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) τ).symm
  have hodd : Odd (orderOf τ) := by rw [hτ]; exact hℓ.odd_of_ne_two hℓ2
  have hq : Odd (Nat.card F) := hF.1
  have hcard := card_fixedSubgroup_of_odd e τ hodd hq
  have hq₀pow : Nat.card (fixedField τ) ^ ℓ = Nat.card F := by
    rw [← hτ]; exact fixedField_card_pow τ
  have hq₀odd : Odd (Nat.card (fixedField τ)) := odd_card_fixedField τ hq
  have hq₀3 : 3 ≤ Nat.card (fixedField τ) := by
    have h1 : 1 < Nat.card (fixedField τ) := by
      have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (fixedField τ))
      exact this
    obtain ⟨m, hm⟩ := hq₀odd
    omega
  set q₀ := Nat.card (fixedField τ) with hq₀
  have hex : ∃ s : ℕ, s.Prime ∧ s ∣ k ∧ ¬ s ∣ q₀ ^ 2 - 1 ∧ s ≠ ℓ ∧ ¬ s ∣ q₀ := by
    rcases hkq with hk | hk
    · obtain ⟨s, hsp, hsd, hs1, hs2, hs3⟩ := exists_prime_dvd_pow_add_one hℓ hℓ2 hq₀odd hq₀3
      exact ⟨s, hsp, by rw [hk, ← hq₀pow]; exact hsd, hs1, hs2, hs3⟩
    · obtain ⟨s, hsp, hsd, hs1, hs2, hs3⟩ := exists_prime_dvd_pow_sub_one hℓ hℓ2 hq₀odd hq₀3
      refine ⟨s, hsp, ?_, hs1, hs2, hs3⟩
      have : k = q₀ ^ ℓ - 1 := by rw [hq₀pow]; omega
      rw [this]; exact hsd
  obtain ⟨s, hsp, hsk, hs1, hs2, hs3⟩ := hex
  have hs2' : s ≠ 2 := by
    rintro rfl
    apply hs1
    have : Even (q₀ ^ 2 - 1) := Nat.Odd.sub_odd hq₀odd.pow (odd_one)
    exact this.two_dvd
  refine ⟨s, hsp, hs2, hXk s hsp hs2' hsk, ?_⟩
  intro x hx hxs hcomm
  rw [← hXu] at hx
  obtain ⟨k₁, hk₁, rfl⟩ := hx
  have hfix : fieldAutHom e τ k₁ = k₁ := by
    apply conj_injective_of_L2 e
    rw [← mul_conj_mul_inv_eq_conj_apply, hcomm]
    group
  have hmem : k₁ ∈ fixedSubgroup K (fieldAutHom e τ) := hfix
  have hok : orderOf k₁ = s := by rw [← orderOf_conj_eq e k₁]; exact hxs
  have hdvd : s ∣ Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)) := by
    rw [← hok]
    have := Subgroup.orderOf_dvd_natCard (fixedSubgroup K (fieldAutHom e τ)) hmem
    exact this
  rw [hcard] at hdvd
  have h3 : s ∣ q₀ * (q₀ ^ 2 - 1) :=
    hdvd.trans (Nat.div_dvd_of_dvd (even_mul_sq_sub_one hq₀odd).two_dvd)
  rcases (Nat.Prime.dvd_mul hsp).mp h3 with h | h
  · exact hs3 h
  · exact hs1 h


theorem ivk_1_3d_aux (hF : L2Field F) (e : K ≃* L2 F) (N : L2Notation e) {u : MulAut K}
    (hu : u ∈ innDiagSub e) (hu2 : orderOf u = 2) (huT : u ∈ (N.T : Subgroup (MulAut K))) :
    ∃ Y : Subgroup (MulAut K), Y ≤ centralizer ({u} : Set (MulAut K)) ∧
      (∀ c ∈ centralizer ({u} : Set (MulAut K)), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) ∧
      Odd (Nat.card ↥Y) ∧
      (∃ k : ℕ, Nat.card ↥Y * 2 ^ k = Nat.card ↥(centralizer ({u} : Set (MulAut K)))) ∧
      (fittingSubgroup ↥Y).map Y.subtype = xuInn u ∧
      (∃ (_ : ((xuInn u).subgroupOf Y).Normal), IsCyclic (↥Y ⧸ (xuInn u).subgroupOf Y)) ∧
      ∃ e' : K ≃* L2 F, Y ≤ xuInn u ⊔ fieldAutSub e' := by
  set C : Subgroup (MulAut K) := centralizer ({u} : Set (MulAut K)) with hC
  set H : Subgroup (MulAut K) := innDiagSub e with hH
  set D : Subgroup (MulAut K) := C ⊓ H with hD
  have hHn : H.Normal := innDiagSub_normal e
  obtain ⟨k, hk3, hkq, ⟨φ⟩⟩ := centralizer_inndiag_dihedral hF e hu hu2
  obtain ⟨X, hXD, hXnormD, hXcyc, hXodd_iff, hXodd, s, hsD⟩ :=
    dihedral_odd_part_sub D (by omega) φ
  have hXeq : xuInn u = X := xuInn_eq_of_odd hF e X hXD hXnormD hXodd_iff hXodd
  subst hXeq
  have hCX : ∀ c ∈ C, ∀ x ∈ xuInn u, c * x * c⁻¹ ∈ xuInn u := by
    intro c hc x hx
    obtain ⟨k₁, hk₁, rfl⟩ := hx
    rw [mul_conj_mul_inv_eq_conj_apply]
    exact ⟨c k₁, apply_mem_xu (Subgroup.mem_centralizer_singleton_iff.mp hc) hk₁, rfl⟩
  have hcyc := exists_generator_centralizer hF e u
  have hCD : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := by
    intro c hc d hd
    have hdC : d ∈ C := hd.1
    have hdH : d ∈ H := hd.2
    exact ⟨Subgroup.mul_mem C (Subgroup.mul_mem C hc hdC) (Subgroup.inv_mem C hc),
      hHn.conj_mem d hdH c⟩
  have hCD' : ∀ c ∈ C, ∀ d ∈ D, c⁻¹ * d * c ∈ D := by
    intro c hc d hd
    have := hCD c⁻¹ (Subgroup.inv_mem C hc) d hd
    simpa using this
  have hK : ∀ c ∈ C, Odd (orderOf c) → ∀ d ∈ D, c * d * c⁻¹ * d⁻¹ ∈ xuInn u := by
    intro c hc hodd d hd
    exact dihedral_normal_odd_comm D (by omega) φ (xuInn u)
      (fun g hg ho => (hXodd_iff g hg).mp ho) c (hCD c hc) (hCD' c hc) hodd d hd
  obtain ⟨Y, hYC, hXY, hYn, hYodd, ⟨k₂, hk₂⟩, hYD, hYodds, -, hlast⟩ :=
    exists_normal_two_complement C D (xuInn u) inf_le_left hXD hCD hCX hXodd ⟨s, hsD⟩ hcyc hK
  obtain ⟨S, hS⟩ := exists_odd_fieldAut hF e
  have hSC : S ≤ C := by
    intro f hf
    obtain ⟨hfF, hfo⟩ := (hS f).mp hf
    exact Subgroup.mem_centralizer_singleton_iff.mpr (N.F_odd_cent f hfF hfo u huT).symm
  have hSY : S ≤ Y := fun f hf => hYodds f (hSC hf) ((hS f).mp hf).2
  have hYXS : ∀ y ∈ Y, ∃ x ∈ xuInn u, ∃ σ ∈ S, y = x * σ := by
    intro y hy
    set τ := fieldProj e y with hτdef
    have hyo : Odd (orderOf y) := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hy)
    have hτo : Odd (orderOf τ) := hyo.of_dvd_nat (orderOf_map_dvd (fieldProj e) y)
    have hφ : fieldAutHom e τ ∈ S := by
      refine (hS _).mpr ⟨⟨τ, rfl⟩, ?_⟩
      rw [orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) τ]
      exact hτo
    refine ⟨y * (fieldAutHom e τ)⁻¹, ?_, fieldAutHom e τ, hφ, by group⟩
    have hmemY : y * (fieldAutHom e τ)⁻¹ ∈ Y := mul_mem hy (inv_mem (hSY hφ))
    have hmemH : y * (fieldAutHom e τ)⁻¹ ∈ H := by
      show _ ∈ innDiagSub e
      rw [mem_innDiagSub_iff, map_mul, map_inv, fieldProj_fieldAutHom]
      simp [τ]
    have hmemC : y * (fieldAutHom e τ)⁻¹ ∈ C := mul_mem (hYC hy) (inv_mem (hSC hφ))
    have : y * (fieldAutHom e τ)⁻¹ ∈ Y ⊓ D := ⟨hmemY, hmemC, hmemH⟩
    rwa [hYD] at this
  have hYle : Y ≤ xuInn u ⊔ fieldAutSub e := by
    intro y hy
    obtain ⟨x, hx, σ, hσ, rfl⟩ := hYXS y hy
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ((hS σ).mp hσ).1)
  have hXnormY : ∀ y ∈ Y, ∀ x ∈ xuInn u, y * x * y⁻¹ ∈ xuInn u :=
    fun y hy x hx => hCX y (hYC hy) x hx
  have hXS : xuInn u ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx' : x ∈ innDiagSub e ⊓ fieldAutSub e := ⟨(hXD hx1).2, ((hS x).mp hx2).1⟩
    rw [innDiagSub_inf_fieldAutSub e] at hx'
    exact hx'
  have hcardD : Nat.card D = 2 * k := by
    have : NeZero k := ⟨by omega⟩
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hXk : ∀ s' : ℕ, s'.Prime → s' ≠ 2 → s' ∣ k → s' ∣ Nat.card (xuInn u) := by
    intro s' hs' hne hdvd
    have h1 : s' ∣ 2 ^ s * Nat.card (xuInn u) := by
      rw [← hsD, hcardD]; exact Dvd.dvd.mul_left hdvd 2
    exact (Nat.Coprime.pow_right s ((Nat.coprime_primes hs' Nat.prime_two).mpr hne)).dvd_of_dvd_mul_left h1
  have hkey : ∀ σ ∈ S, ∀ ℓ : ℕ, ℓ.Prime → orderOf σ = ℓ →
      ∃ s' : ℕ, s'.Prime ∧ s' ≠ ℓ ∧ s' ∣ Nat.card (xuInn u) ∧
        ∀ x ∈ xuInn u, orderOf x = s' → σ * x ≠ x * σ := by
    intro σ hσ ℓ hℓ hσℓ
    obtain ⟨hσF, hσo⟩ := (hS σ).mp hσ
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      rw [hσℓ] at hσo
      exact absurd hσo (by decide)
    exact exists_noncommuting_prime hF e (xuInn u) rfl hkq hXk hσF hℓ hσℓ hℓ2
  refine ⟨Y, hYC, hYn, hYodd, ⟨k₂, hk₂⟩, ?_, hlast, e, hYle⟩
  exact le_antisymm
    (fitting_le_of_no_commute Y (xuInn u) S hXY hSY hXnormY hXcyc hXS hYXS hkey)
    (le_fitting_map Y (xuInn u) hXY hXnormY hXcyc)

theorem ivk_1_3d : IVK_1_3d := by
  intro F _ _ hF K _ _ e u hu hu2
  obtain ⟨e₁, N, huT, hH⟩ := exists_notation_containing hF e hu2
  exact ivk_1_3d_aux hF e₁ N (by rw [hH]; exact hu) hu2 huT

end Lemma13dMain

end CFSG.GH74.GLS.IVK.Proofs2
