module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.LiftOrbitRel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrbit
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitRoot

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem odd_geomSum {p e : ℕ} (hodd : Odd p) (he : Odd e) : Odd (∑ i ∈ Finset.range e, p ^ i) := by
  have : ∀ n : ℕ, (∑ i ∈ Finset.range n, p ^ i) % 2 = n % 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, (Nat.odd_iff.1 (Odd.pow hodd : Odd (p ^ n)))]
      omega
  rw [Nat.odd_iff, this]
  exact Nat.odd_iff.1 he

theorem card_filter_isSquare_le {F : Type} [Field F] [Fintype F] [DecidableEq F] {p e : ℕ} [Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) (hF : Fintype.card F = p ^ e) (he : Odd e) :
    ((Finset.Ico 1 p).filter (fun m : ℕ => IsSquare (m : F))).card ≤ (p - 1) / 2 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hFchar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨S, hS, hSodd⟩ : ∃ S : ℕ, p ^ e - 1 = (p - 1) * S ∧ Odd S := by
    refine ⟨∑ i ∈ Finset.range e, p ^ i, ?_, odd_geomSum hodd he⟩
    have h1 := Nat.geomSum_eq hp.two_le e
    rw [h1]
    exact (Nat.mul_div_cancel' (by simpa using Nat.sub_dvd_pow_sub_pow p 1 e)).symm
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * k := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hk' : (p - 1) / 2 = k := by omega
  have hpe : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have hq : p ^ e = 2 * (k * S) + 1 := by
    have : p ^ e - 1 = 2 * (k * S) := by rw [hS, hk]; ring
    omega
  have hqd : Fintype.card F / 2 = k * S := by
    rw [hF, hq]
    exact (Nat.mul_add_div (by norm_num : 0 < 2) (k * S) 1).trans (by norm_num)
  have hkpos : 0 < k := by have := hp.two_le; omega
  let φ : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have key : ∀ m ∈ (Finset.Ico 1 p).filter (fun m : ℕ => IsSquare (m : F)),
      ((m : ZMod p)) ∈ Polynomial.nthRootsFinset k (1 : ZMod p) := by
    intro m hm
    obtain ⟨hmI, hmS⟩ := Finset.mem_filter.1 hm
    obtain ⟨hm1, hmp⟩ := Finset.mem_Ico.1 hmI
    have hm0 : (m : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    have hcast : φ (m : ZMod p) = (m : F) := map_natCast φ m
    have hF0 : (m : F) ≠ 0 := by
      rw [← hcast]
      exact (map_ne_zero φ).2 hm0
    rw [Polynomial.mem_nthRootsFinset hkpos]
    have h1 := (FiniteField.isSquare_iff hFchar hF0).1 hmS
    rw [hqd, pow_mul, ← hcast, ← map_pow] at h1
    have ht2 : ((m : ZMod p) ^ k) * ((m : ZMod p) ^ k) = 1 := by
      rw [← pow_add, ← two_mul, ← hk]
      exact ZMod.pow_card_sub_one_eq_one hm0
    rcases mul_self_eq_one_iff.1 ht2 with h | h
    · exact h
    · exfalso
      rw [h, map_neg, map_one, Odd.neg_one_pow hSodd] at h1
      exact Ring.neg_one_ne_one_of_char_ne_two hFchar h1
  have hinj : Set.InjOn (fun m : ℕ => (m : ZMod p)) ↑((Finset.Ico 1 p).filter
      (fun m : ℕ => IsSquare (m : F))) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_Ico.1 (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).1)
    have hb' := (Finset.mem_Ico.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1)
    have := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
    rwa [Nat.mod_eq_of_lt ha'.2, Nat.mod_eq_of_lt hb'.2] at this
  calc ((Finset.Ico 1 p).filter (fun m : ℕ => IsSquare (m : F))).card
      ≤ (Polynomial.nthRootsFinset k (1 : ZMod p)).card :=
        Finset.card_le_card_of_injOn (fun m : ℕ => (m : ZMod p)) key hinj
    _ ≤ k := by
        rw [Polynomial.nthRootsFinset_def]
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    _ = (p - 1) / 2 := hk'.symm

section Count

open scoped Classical

variable {F : Type} [Field F] {ε : ℕ} {p : ℕ} [Fact p.Prime] [Fintype F]

theorem card_fiber_le_addHom_sq (N : ℕ)
    (hsq : ∀ T : Finset ℕ, (∀ m ∈ T, 1 ≤ m ∧ m < p ∧ IsSquare (m : F)) → T.card ≤ N)
    (l : UP F ε →+ ZMod p) (hl : ∃ a, l (0, a) ≠ 0)
    (x₀ : (Fin ε → F) × Fˣ) :
    (Finset.univ.filter (fun x : (Fin ε → F) × Fˣ => kerTau l x = kerTau l x₀)).card ≤
      2 * N := by
  obtain ⟨d₀, μ₀⟩ := x₀
  set lF : F →+ ZMod p := l.comp (AddMonoidHom.inr (Fin ε → F) F) with hlF
  have hlF' : ∃ a, lF a ≠ 0 := hl
  have hμ₀ : (μ₀ : F) ≠ 0 := μ₀.ne_zero
  have hlFμ : ∀ (μ : F), μ ≠ 0 → ∃ a, lF (μ * a) ≠ 0 := by
    intro μ hμ
    obtain ⟨b, hb⟩ := hlF'
    exact ⟨μ⁻¹ * b, by rwa [mul_inv_cancel_left₀ hμ]⟩
  have hτ₀ : l.comp (utau d₀ (μ₀ : F)) ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hlFμ ((μ₀ : F) ^ 2) (pow_ne_zero 2 hμ₀)
    apply ha
    have := DFunLike.congr_fun h0 (0, a)
    rw [AddMonoidHom.comp_apply, utau_zero_prod, AddMonoidHom.zero_apply] at this
    exact this
  let T₀ : Finset ℕ := (Finset.Ico 1 p).filter (fun m : ℕ => IsSquare (m : F))
  have hT₀ : T₀.card ≤ N := hsq T₀ fun m hm => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hm
    obtain ⟨h3, h4⟩ := Finset.mem_Ico.1 h1
    exact ⟨h3, h4, h2⟩
  let R : Finset F := T₀.biUnion
    (fun m => Finset.univ.filter (fun μ : F => μ ^ 2 = (m : F) * (μ₀ : F) ^ 2))
  have hR : R.card ≤ 2 * N := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ m ∈ T₀,
          (Finset.univ.filter (fun μ : F => μ ^ 2 = (m : F) * (μ₀ : F) ^ 2)).card
        ≤ ∑ _m ∈ T₀, 2 := Finset.sum_le_sum fun m _ => card_filter_sq_le _
      _ = 2 * T₀.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * N := Nat.mul_le_mul_left _ hT₀
  have hprop : ∀ x : (Fin ε → F) × Fˣ, kerTau l x = kerTau l (d₀, μ₀) →
      ∃ k : ZMod p, ∀ y, l (utau x.1 (x.2 : F) y) = k * l (utau d₀ (μ₀ : F) y) := by
    intro x hx
    refine exists_smul_of_ker_eq_addHom (l.comp (utau d₀ (μ₀ : F))) (l.comp (utau x.1 (x.2 : F)))
      hτ₀ fun y => ?_
    have := SetLike.ext_iff.1 hx y
    simpa [kerTau] using this.symm
  have hmem : ∀ x : (Fin ε → F) × Fˣ, kerTau l x = kerTau l (d₀, μ₀) → (x.2 : F) ∈ R := by
    intro x hx
    obtain ⟨k, hk⟩ := hprop x hx
    have h1 : ∀ b : F, lF (((x.2 : F) ^ 2 / (μ₀ : F) ^ 2) * b) = k * lF b := by
      intro b
      have := hk (0, b / (μ₀ : F) ^ 2)
      rw [utau_zero_prod, utau_zero_prod] at this
      have e1 : (x.2 : F) ^ 2 * (b / (μ₀ : F) ^ 2) = ((x.2 : F) ^ 2 / (μ₀ : F) ^ 2) * b := by
        field_simp
      have e2 : (μ₀ : F) ^ 2 * (b / (μ₀ : F) ^ 2) = b := by field_simp
      rw [e2, e1] at this
      exact this
    have h2 := eq_natCast_of_map_mul_eq lF hlF' h1
    have hxne : (x.2 : F) ≠ 0 := x.2.ne_zero
    have h3 : (x.2 : F) ^ 2 = (k.val : F) * (μ₀ : F) ^ 2 := by
      field_simp at h2
      linear_combination h2
    have hk0 : k.val ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_mul] at h3
      exact pow_ne_zero 2 hxne h3
    refine Finset.mem_biUnion.2 ⟨k.val, ?_, ?_⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨Nat.pos_of_ne_zero hk0, ZMod.val_lt k⟩, ?_⟩
      refine ⟨(x.2 : F) / (μ₀ : F), ?_⟩
      have : (k.val : F) = (x.2 : F) ^ 2 / (μ₀ : F) ^ 2 := by
        field_simp
        linear_combination -h3
      rw [this]
      field_simp
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h3⟩
  have hlF_zero : ∀ ξ : F, (∀ r : F, lF (ξ * r) = 0) → ξ = 0 := by
    intro ξ hξ
    by_contra hξ0
    obtain ⟨b, hb⟩ := hlF'
    apply hb
    have := hξ (ξ⁻¹ * b)
    rwa [mul_inv_cancel_left₀ hξ0] at this
  have hlF_def : ∀ a : F, lF a = l (0, a) := fun a => rfl
  have hinj : Set.InjOn (fun x : (Fin ε → F) × Fˣ => (x.2 : F))
      ↑(Finset.univ.filter (fun x : (Fin ε → F) × Fˣ => kerTau l x = kerTau l (d₀, μ₀))) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    obtain ⟨k₁, hk₁⟩ := hprop x hx'
    obtain ⟨k₂, hk₂⟩ := hprop y hy'
    have hxy' : (x.2 : F) = (y.2 : F) := hxy
    have hkk : k₁ = k₂ := by
      obtain ⟨a, ha⟩ := hlFμ ((μ₀ : F) ^ 2) (pow_ne_zero 2 hμ₀)
      have e1 := hk₁ (0, a)
      have e2 := hk₂ (0, a)
      rw [utau_zero_prod, utau_zero_prod, ← hlF_def, ← hlF_def] at e1 e2
      rw [hxy'] at e1
      have e3 : (k₁ - k₂) * lF ((μ₀ : F) ^ 2 * a) = 0 := by
        rw [sub_mul, ← e1, ← e2, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_right ha)
    subst hkk
    have hsame : ∀ z, l (utau x.1 (x.2 : F) z) = l (utau y.1 (y.2 : F) z) := fun z => by
      rw [hk₁, hk₂]
    have key : ∀ (w : Fin ε → F) (a₁ a₂ : F), l (w, a₁) = l (w, a₂) → lF (a₁ - a₂) = 0 := by
      intro w a₁ a₂ h
      rw [hlF_def]
      have : ((0 : Fin ε → F), a₁ - a₂) = (w, a₁) - (w, a₂) := by
        refine Prod.ext (funext fun j => by simp) (by simp)
      rw [this, map_sub, h]
      exact sub_self _
    have hd : x.1 = y.1 := by
      funext i
      have hξ : (x.2 : F) * (x.1 i - y.1 i) = 0 := by
        refine hlF_zero _ fun r => ?_
        have h1 := hsame (Pi.single i r, 0)
        rw [utau_single, utau_single, ← hxy'] at h1
        have e : (x.2 : F) * (x.1 i - y.1 i) * r =
            (x.2 : F) * (x.1 i * r) - (x.2 : F) * (y.1 i * r) := by ring
        rw [e]
        exact key _ _ _ h1
      exact sub_eq_zero.1 ((mul_eq_zero.1 hξ).resolve_left x.2.ne_zero)
    exact Prod.ext hd (Units.ext hxy')
  calc (Finset.univ.filter (fun x : (Fin ε → F) × Fˣ => kerTau l x = kerTau l (d₀, μ₀))).card
      ≤ R.card := Finset.card_le_card_of_injOn (fun x : (Fin ε → F) × Fˣ => (x.2 : F))
        (fun x hx => hmem x (Finset.mem_filter.1 hx).2) hinj
    _ ≤ 2 * N := hR

theorem card_params_le_mul_card_image_sq (N : ℕ)
    (hsq : ∀ T : Finset ℕ, (∀ m ∈ T, 1 ≤ m ∧ m < p ∧ IsSquare (m : F)) → T.card ≤ N)
    (l : UP F ε →+ ZMod p) (hl : ∃ a, l (0, a) ≠ 0) :
    Nat.card F ^ ε * (Nat.card F - 1) ≤
      2 * N * ((Finset.univ : Finset ((Fin ε → F) × Fˣ)).image (kerTau l)).card := by
  have h := Finset.card_le_mul_card_image (Finset.univ : Finset ((Fin ε → F) × Fˣ))
    (f := kerTau l) (2 * N) (fun a ha => by
      obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 ha
      exact card_fiber_le_addHom_sq N hsq l hl x₀)
  rwa [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_units, ← Nat.card_eq_fintype_card] at h

end Count

section Param

open scoped Classical

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {F : Type} [Field F] [Fintype F] {ε : ℕ} {p : ℕ} [Fact p.Prime]
  {S : Type} [Group S] [Finite S]

theorem horb_of_param_sq (N : ℕ)
    (hsq : ∀ T : Finset ℕ, (∀ m ∈ T, 1 ≤ m ∧ m < p ∧ IsSquare (m : F)) → T.card ≤ N)
    (ψ : Multiplicative (UP F ε) →* S) (t : (Fin ε → F) → Fˣ → S)
    (ht : ∀ d μ x, t d μ * ψ x * (t d μ)⁻¹ =
      ψ (Multiplicative.ofAdd (utau d (μ : F) (Multiplicative.toAdd x))))
    {D₀ : Subgroup S} (hrel : D₀.relIndex ψ.range = p)
    (hZ : ¬ ((ψ.comp (AddMonoidHom.inr (Fin ε → F) F).toMultiplicative).range ≤ D₀)) :
    Nat.card F ^ ε * (Nat.card F - 1) ≤ 2 * N *
      (Subgroup.normalizer (ψ.range : Set S) ⊓ Subgroup.normalizer (D₀ : Set S)).relIndex
        (Subgroup.normalizer (ψ.range : Set S)) := by
  have hT : ∀ d μ, t d μ ∈ Subgroup.normalizer (ψ.range : Set S) := by
    intro d μ
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (ht d μ x).symm⟩
    · rintro ⟨x', hx'⟩
      obtain ⟨z, hz⟩ := utau_surjective d μ.ne_zero (Multiplicative.toAdd x')
      refine ⟨Multiplicative.ofAdd z, ?_⟩
      have h1 : t d μ * ψ (Multiplicative.ofAdd z) * (t d μ)⁻¹ = ψ x' := by
        rw [ht, toAdd_ofAdd, hz, ofAdd_toAdd]
      have h2 : t d μ * ψ (Multiplicative.ofAdd z) * (t d μ)⁻¹ = t d μ * y * (t d μ)⁻¹ := by
        rw [h1, hx']
      exact mul_left_cancel (mul_right_cancel h2)
  have hDidx : (D₀.comap ψ).index = p := by
    rw [Subgroup.index_comap]
    exact hrel
  have hDaidx : (AddSubgroup.toSubgroup.symm (D₀.comap ψ)).index = p := by
    rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply]
    exact hDidx
  obtain ⟨l, hl⟩ := exists_hom_of_index_eq_prime _ hDaidx
  have hlD : ∀ z : UP F ε, l z = 0 ↔ ψ (Multiplicative.ofAdd z) ∈ D₀ := fun z =>
    (hl z).trans (mem_toSubgroup_symm _ z)
  have hlz : ∃ a, l (0, a) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hZ
    rintro _ ⟨y, rfl⟩
    exact (hlD (0, Multiplicative.toAdd y)).1 (hcon _)
  have hker : ∀ x : (Fin ε → F) × Fˣ, kerTau l x =
      AddSubgroup.toSubgroup.symm ((conjSub (t x.1 x.2)⁻¹ D₀).comap ψ) := by
    intro x
    ext z
    rw [kerTau, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hlD, mem_toSubgroup_symm,
      Subgroup.mem_comap, mem_conjSub, inv_inv, ht x.1 x.2 (Multiplicative.ofAdd z), toAdd_ofAdd]
  let s : Finset S := Finset.univ.image (fun x : (Fin ε → F) × Fˣ => (t x.1 x.2)⁻¹)
  have hs : ∀ y ∈ s, y ∈ Subgroup.normalizer (ψ.range : Set S) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact (Subgroup.normalizer (ψ.range : Set S)).inv_mem (hT _ _)
  have h1 := card_image_conj_le_relIndex (Subgroup.normalizer (ψ.range : Set S)) D₀ s hs
  let G : Subgroup S → AddSubgroup (UP F ε) := fun C => AddSubgroup.toSubgroup.symm (C.comap ψ)
  have hcomp : (Finset.univ.image (kerTau l)) =
      (s.image fun y => conjSub y D₀).image G := by
    simp only [s, Finset.image_image]
    congr 1
    funext x
    exact hker x
  have h2 : (Finset.univ.image (kerTau l)).card ≤ (s.image fun y => conjSub y D₀).card := by
    rw [hcomp]
    exact Finset.card_image_le
  exact (card_params_le_mul_card_image_sq N hsq l hlz).trans (Nat.mul_le_mul_left _ (h2.trans h1))

end Param

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LinearGroups

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_psun_full (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ e) ^ 2) (heo : Odd e) (hn : 3 ≤ n) {L : Subgroup (MulAut W)}
    (π : ↥L →* StatedProj (StatedSU n (p ^ e) K)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) * (p ^ e) ^ (n - 2) / (p - 1))) ≤
      Nat.card W := by
  have he : 1 ≤ e := by
    by_contra hlt
    have he0 : e = 0 := by omega
    have h1 : Nat.card K = 1 := by rw [hK, he0]; simp
    have h2 := Finite.one_lt_card (α := K)
    omega
  have hU : UnitaryFieldData p e K := ⟨Fact.out, he, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨ε, rfl⟩ : ∃ ε, n = 2 * 1 + ε := ⟨n - 2, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport hU (r := 1) (ε := ε)
  have hn1 : 1 ≤ 2 * 1 + ε := by omega
  let ι := hypPSUEquivStatedProj hU hR hn1
  let π' : ↥L →* hypPSU hU 1 ε := (ι.symm : _ →* _).comp π
  have hπ' : Function.Surjective π' := ι.symm.surjective.comp hπ
  have hker_eq : π'.ker = π.ker := by
    ext x
    simp [π', MonoidHom.mem_ker]
  obtain ⟨τ₀, hτE, hτ0⟩ := hU.exists_mem_traceZero_ne_zero
  have hbar : hU.bar τ₀ = -τ₀ := by
    have := hU.mem_traceZero.1 hτE
    rw [UnitaryFieldData.trace] at this
    linear_combination this
  have two_ne : (2 : K) ≠ 0 := by
    intro h2
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff K p] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h3)
  have hc : UCtx hU τ₀ := ⟨hbar, hτ0, two_ne⟩
  let _ : Fintype hU.fixedField := Fintype.ofFinite _
  let ψ : Multiplicative (UP hU.fixedField ε) →* hypPSU hU 1 ε :=
    (hypProj hU 1 ε).comp (uPar hc)
  have hψ : Function.Injective ψ := uPar_inj hc
  have hFcard : Nat.card hU.fixedField = p ^ e := hU.card_fixedField
  have hpF : ∀ y : UP hU.fixedField ε, p • y = 0 := by
    intro y
    refine Prod.ext (funext fun l => ?_) ?_
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      simp
  have hZne : (ψ.comp (AddMonoidHom.inr (Fin ε → hU.fixedField) hU.fixedField).toMultiplicative).range
      ≠ ⊥ := by
    intro h0
    have hmem : ψ (Multiplicative.ofAdd ((0 : Fin ε → hU.fixedField), (1 : hU.fixedField))) ∈
        (ψ.comp (AddMonoidHom.inr (Fin ε → hU.fixedField) hU.fixedField).toMultiplicative).range :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    have h1 := hψ (hmem.trans (map_one ψ).symm)
    exact one_ne_zero (congrArg (fun z : Multiplicative (UP hU.fixedField ε) =>
      (Multiplicative.toAdd z).2) h1)
  have hUc : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (mul_comm x y)
  have hUp : ∀ a ∈ ψ.range, a ^ p = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := by
      rw [← ofAdd_toAdd x, ← ofAdd_nsmul, hpF]
      rfl
    rw [this, map_one]
  have ht : ∀ (d : Fin ε → hU.fixedField) (μ : (hU.fixedField)ˣ)
      (x : Multiplicative (UP hU.fixedField ε)),
      hypProj hU 1 ε (tPar hc d μ) * ψ x * (hypProj hU 1 ε (tPar hc d μ))⁻¹ =
        ψ (Multiplicative.ofAdd (utau d (μ : hU.fixedField) (Multiplicative.toAdd x))) := by
    intro d μ x
    simp only [ψ, MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, tPar_conj hc]
  have hfin : Finite (hypPSU hU 1 ε) := inferInstance
  have hsq : ∀ T : Finset ℕ, (∀ m ∈ T, 1 ≤ m ∧ m < p ∧ IsSquare (m : hU.fixedField)) →
      T.card ≤ (p - 1) / 2 := by
    classical
    intro T hT
    have hc : Fintype.card hU.fixedField = p ^ e := by
      rw [← Nat.card_eq_fintype_card]; exact hFcard
    have : CharP hU.fixedField p := inferInstance
    refine (Finset.card_le_card (t := (Finset.Ico 1 p).filter
      (fun m : ℕ => IsSquare (m : hU.fixedField))) fun m hm => ?_).trans
      (card_filter_isSquare_le hp2 hc heo)
    obtain ⟨h1, h2, h3⟩ := hT m hm
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨h1, h2⟩, h3⟩
  have key := FFToolkit.two_pow_le_card_of_lift_orbit_rel hW hp2 π' hπ'
    (by rw [hker_eq]; exact hker) (by rw [hker_eq]; exact hZ)
    (Z := (ψ.comp (AddMonoidHom.inr (Fin ε → hU.fixedField) hU.fixedField).toMultiplicative).range)
    (U₀ := ψ.range) (T₀ := Subgroup.normalizer (ψ.range : Set (hypPSU hU 1 ε)))
    (m := (p ^ e - 1) * (p ^ e) ^ ε / (p - 1))
    (fun z ⟨y, hy⟩ => ⟨_, hy⟩) hZne hUc hUp le_rfl (fun D₀ _ hrel hZD => by
      have := horb_of_param_sq ((p - 1) / 2) hsq ψ (fun d μ => hypProj hU 1 ε (tPar hc d μ)) ht
        hrel hZD
      rw [hFcard] at this
      have h2 : 2 * ((p - 1) / 2) = p - 1 := by
        have := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
        obtain ⟨k, hk⟩ := this
        omega
      rw [h2] at this
      exact Nat.div_le_of_le_mul (by rw [mul_comm (p ^ e - 1)]; exact this))
  have e2 : 2 * 1 + ε - 2 = ε := by omega
  rw [e2, mul_comm]
  exact key

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
