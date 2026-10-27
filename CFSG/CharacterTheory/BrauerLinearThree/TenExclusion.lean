module

public import CFSG.CharacterTheory.BrauerLinearThree.TenColumn
public import CFSG.CharacterTheory.BrauerLinearThree.TenInvolutions
public import CFSG.CharacterTheory.BrauerLinearThree.TenCentralizer

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.Semidihedral.Principal
open CFSG.Semidihedral (r s)

theorem exists_prime_factorization_lt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : ¬ a ∣ b) :
    ∃ p : ℕ, p.Prime ∧ b.factorization p < a.factorization p := by
  rw [← Nat.factorization_le_iff_dvd ha hb, Finsupp.le_def] at h
  push Not at h
  obtain ⟨p, hp⟩ := h
  refine ⟨p, ?_, hp⟩
  by_contra hnp
  rw [Nat.factorization_eq_zero_of_not_prime a hnp] at hp
  omega

theorem exists_character_orderOf {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {d : ℕ}
    (hd : d ∣ Nat.card Q) : ∃ χ : Q →* ℂˣ, orderOf χ = d := by
  let : CommGroup Q := IsCyclic.commGroup
  have : NeZero ((Nat.card Q : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Q ℂ
  have : Finite (Q →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  have : IsCyclic (Q →* ℂˣ) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcard : Nat.card (Q →* ℂˣ) = Nat.card Q := Nat.card_congr e.toEquiv
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q →* ℂˣ)
  have hpos : 0 < Nat.card (Q →* ℂˣ) := Nat.card_pos
  obtain ⟨k, hk⟩ := hcard ▸ hd
  have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; omega
  refine ⟨g ^ k, ?_⟩
  rw [orderOf_pow_of_dvd hk0 ⟨d, by rw [hg, hk, mul_comm]⟩, hg, hk,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]

theorem exists_torus_column_relation
    {G : Type} [Group G] [Fintype G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2)
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    ¬ Nat.card W ∣ (W.subgroupOf K).index →
    ∃ (ρ : basis.index) (δ A : ℤ), (A = 9 ∨ A = 5) ∧ (A = 9 → ¬ Nat.card W ∣ 3) ∧
      (A = 5 → ¬ Nat.card W ∣ 15) ∧ (δ = 1 ∨ δ = -1) ∧ ρ ≠ principal ∧
      Odd (Module.finrank ℂ (basis.representation ρ).vector) ∧
      (∀ g, starRingEnd ℂ ((basis.representation ρ).character g) =
        (basis.representation ρ).character g) ∧
      3 * (Nat.card G : ℂ) * ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) -
          (basis.representation ρ).character t) ^ 2 =
        A * Nat.card W * (Nat.card (C t) : ℂ) ^ 2 *
          ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) *
            ((Module.finrank ℂ (basis.representation ρ).vector : ℂ) + δ)) := by
  intro s₀ V D W K hndvd
  set H : Subgroup G := Subgroup.normalizer (W : Set G) with hHdef
  obtain ⟨-, ht2, -, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨-, hW1, hWcyc, hWodd, -, -, -, -, -, ⟨d₀, -, -, -, -, -, ⟨eD⟩, -, P₀, hP₀⟩, -, -, -,
      hKH, hinvH, -, -, -, hOK, -, -, ⟨hcases, -⟩, -, -, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hKH : K.relIndex H = 2 := hKH
  have hinvH : ∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹ := hinvH
  have hOK : (CFSG.pPrimeCore 2 K).map K.subtype = W := hOK
  have hcases : (Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
        Nat.card K = 12 * Nat.card W ∧ Nat.card H = 24 * Nat.card W) ∨
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
        Nat.card K = 60 * Nat.card W ∧ Nat.card H = 120 * Nat.card W) := hcases
  have hdih : ∃ P : Sylow 2 H, Nonempty ((P : Subgroup H) ≃* DihedralGroup 4) :=
    ⟨P₀, ⟨(Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      ((MulEquiv.subgroupCongr hP₀).trans eD)⟩⟩
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hWcomm x hx w hw
  have hKH' : K ≤ H := Subgroup.centralizer_le_normalizer _
  have hcentK : ∀ k ∈ K, ∀ w ∈ W, k * w = w * k := fun k hk w hw =>
    (Subgroup.mem_centralizer_iff.mp hk w hw).symm
  have hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : h⁻¹ * w * h⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (H.inv_mem hh) w).mp hw
    rw [inv_inv] at hw'
    have hc := hcentK k hk _ hw'
    calc w * (h * k * h⁻¹) = h * ((h⁻¹ * w * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * w * h)) * h⁻¹ := by rw [hc]
      _ = h * k * h⁻¹ * w := by group
  have hHK : Nat.card H = 2 * Nat.card K := by
    have h := Subgroup.card_mul_index (K.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH').toEquiv] at h
    have hri : (K.subgroupOf H).index = 2 := hKH
    rw [hri] at h
    omega
  have hKH2 : ∀ x ∈ H, ∀ y ∈ H, x ∉ K → y ∉ K → x * y ∈ K := by
    intro x hx y hy hxK hyK
    have hri : (K.subgroupOf H).index = 2 := hKH
    have h := (Subgroup.mul_mem_iff_of_index_two hri (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
      (iff_of_false (by rw [Subgroup.mem_subgroupOf]; exact hxK)
        (by rw [Subgroup.mem_subgroupOf]; exact hyK))
    rwa [Subgroup.mem_subgroupOf] at h
  have hCU := centralizer_eq_of_le_torus n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel hN hY
  have hCK : ∀ x ∈ W, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = K := by
    intro x hx hx1
    have h := hCU (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hx)
      (by rwa [Ne, Subgroup.zpowers_eq_bot])
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  have hTI : ∀ g : G, ∀ w ∈ W, w ≠ 1 → g * w * g⁻¹ ∈ W → g ∈ H := fun g w hw hw1 hgw =>
    mem_normalizer_of_conj_mem hOK hCK hw hw1 hgw
  have hW0 : Nat.card W ≠ 0 := Nat.card_pos.ne'
  have he0 : (W.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨p₀, hp₀, hlt⟩ := exists_prime_factorization_lt hW0 he0 hndvd
  set v := (Nat.card W).factorization p₀ with hvdef
  obtain ⟨χ, hχ⟩ := exists_character_orderOf (Q := W) (Nat.ordProj_dvd (Nat.card W) p₀)
  have hp₀odd : Odd p₀ := by
    have hv1 : 1 ≤ v := by omega
    have hdvd : p₀ ∣ Nat.card W :=
      (dvd_pow_self p₀ (by omega)).trans (Nat.ordProj_dvd (Nat.card W) p₀)
    exact hWodd.of_dvd_nat hdvd
  have hχodd : Odd (orderOf χ) := by rw [hχ]; exact hp₀odd.pow
  have hχe : χ ^ (W.subgroupOf K).index ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one (G := W →* ℂˣ) h
    rw [hχ] at hdvd
    have := (hp₀.pow_dvd_iff_le_factorization he0).mp hdvd
    omega
  obtain ⟨w₀', hw₀'⟩ : ∃ w : W, (χ ^ (W.subgroupOf K).index) w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hχe (MonoidHom.ext hcon)
  have hw₀ : (w₀' : G) ∈ W := w₀'.2
  have hw₀1 : TenColumn.torusTransfer hWK χ ⟨w₀', hWK hw₀⟩ ≠ 1 := by
    rw [TenColumn.torusTransfer_apply hWK hcentK χ]
    rw [MonoidHom.pow_apply, ← map_pow] at hw₀'
    convert hw₀' using 2
  have hinvol : ∀ x : G, orderOf x = 2 ↔ IsConj x t := by
    obtain ⟨-, -, h⟩ := CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn
      S fS
    have hz : (((fS (r n)) ^ 2 ^ (n - 2) : S) : G) = t := by rw [ht, Subgroup.coe_pow]
    intro x
    rw [← hz]
    exact h Group.IsPerfect.commutator_eq_top x
  obtain ⟨ρ, δ, hδ, hρo, hρodd, hpos, hρr, hcol⟩ :=
    TenColumn.exists_odd_column hWK hKH' hcentK hinvH hKn hHK hKH2 hTI χ hχodd hw₀ hw₀1 ht2
      hinvol basis principal hprincipal
  set F : ℂ := (Module.finrank ℂ (basis.representation ρ).vector : ℂ) with hF
  set x : ℂ := (basis.representation ρ).character t with hx
  have hF0 : F ≠ 0 := Nat.cast_ne_zero.mpr hρodd.pos.ne'
  have hFδ0 : F + δ ≠ 0 := by
    have h : ((Module.finrank ℂ (basis.representation ρ).vector : ℤ) + δ : ℤ) ≠ 0 := hpos.ne'
    rw [hF]
    exact_mod_cast h
  have hkey : ∀ (ι κ A : ℕ), (3 * ι ^ 2 = A * κ) →
      ((TenColumn.outerInvolutions K H).card = Nat.card W * ι) → Nat.card K = κ * Nat.card W →
      3 * (Nat.card G : ℂ) * (F - x) ^ 2 =
        (A : ℂ) * Nat.card W * (Nat.card (C t) : ℂ) ^ 2 * (F * (F + δ)) := by
    intro ι κ A hA hI hKc
    rw [hI, hKc] at hcol
    have hW0' : (Nat.card W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW0
    have hκ0 : (κ : ℂ) ≠ 0 := by
      intro h0
      have : Nat.card K = 0 := by rw [hKc]; exact_mod_cast (by simpa using h0 : κ * Nat.card W = 0)
      exact Nat.card_pos.ne' this
    have hAC : (3 : ℂ) * (ι : ℂ) ^ 2 = (A : ℂ) * κ := by exact_mod_cast hA
    push_cast at hcol
    rw [← mul_div_assoc, div_eq_div_iff (mul_ne_zero hF0 hFδ0) (mul_ne_zero hκ0 hW0')] at hcol
    have h3 : (3 * (Nat.card G : ℂ) * (F - x) ^ 2) * ((κ : ℂ) * Nat.card W) =
        ((A : ℂ) * Nat.card W * (Nat.card (C t) : ℂ) ^ 2 * (F * (F + δ))) *
          ((κ : ℂ) * Nat.card W) := by
      linear_combination 3 * hcol + (Nat.card (C t) : ℂ) ^ 2 * (Nat.card W : ℂ) ^ 2 *
        (F * (F + δ)) * hAC
    exact mul_right_cancel₀ (mul_ne_zero hκ0 hW0') h3
  have hindex : ∀ κ : ℕ, Nat.card K = κ * Nat.card W → (W.subgroupOf K).index = κ := by
    intro κ hKc
    have h := Subgroup.card_mul_index (W.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv, hKc] at h
    have hW0'' : 0 < Nat.card W := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hW0'' (by linarith)
  rcases hcases with ⟨hA4, hK12, -⟩ | ⟨hA5, hK60, -⟩
  · have hI := TenColumn.card_outerInvolutions_eq W hWodd hWcomm hKH hinvH hOK (d := 4)
      (Or.inl rfl) hA4 hdih
    refine ⟨ρ, δ, 9, Or.inl rfl, fun _ h3 => hndvd ?_, fun h => absurd h (by norm_num), hδ, hρo,
      hρodd, hρr, ?_⟩
    · rw [hindex 12 hK12]
      exact h3.trans (by norm_num)
    · have h := hkey 6 12 9 (by norm_num) (by rw [hI]; rfl) hK12
      rw [← hF, ← hx]
      push_cast at h ⊢
      exact h
  · obtain ⟨e5⟩ := LargePrimeTorus.nonempty_equiv_alternating_five_of_model hA5
    have hI := TenColumn.card_outerInvolutions_eq W hWodd hWcomm hKH hinvH hOK (d := 5)
      (Or.inr rfl) ⟨e5⟩ hdih
    refine ⟨ρ, δ, 5, Or.inr rfl, fun h => absurd h (by norm_num), fun _ h15 => hndvd ?_, hδ, hρo,
      hρodd, hρr, ?_⟩
    · rw [hindex 60 hK60]
      exact h15.trans (by norm_num)
    · have h := hkey 10 60 5 (by norm_num) (by rw [hI]; rfl) hK60
      rw [← hF, ← hx]
      push_cast at h ⊢
      exact h

end CFSG.BrauerLinearThree
