module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Model
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Goldschmidt

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.GorensteinWalter
open scoped MatrixGroups

section Field

variable {K : Type*} [Field K]

theorem card_fix_sq_of_two_ne_zero [Finite K] (h2 : (2 : K) ≠ 0) (θ : K →+* K)
    (hθ : ∀ x, θ (θ x) = x) {e : K} (he : θ e ≠ e) :
    Nat.card {x : K // θ x = x} ^ 2 = Nat.card K := by
  have hd0 : e - θ e ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  have hθd : θ (e - θ e) = -(e - θ e) := by
    rw [map_sub, hθ]
    ring
  have h2θ : θ 2 = 2 := map_ofNat θ 2
  set d := e - θ e with hd
  have hdec1 : ∀ x : K, θ ((x + θ x) / 2) = (x + θ x) / 2 := fun x => by
    rw [map_div₀, map_add, hθ, h2θ, add_comm]
  have hdec2 : ∀ x : K, θ ((x - θ x) / (2 * d)) = (x - θ x) / (2 * d) := fun x => by
    rw [map_div₀, map_sub, hθ, map_mul, h2θ, hθd]
    field_simp
    ring
  let f : {x : K // θ x = x} × {x : K // θ x = x} → K := fun p => (p.1 : K) + (p.2 : K) * d
  let g : K → {x : K // θ x = x} × {x : K // θ x = x} := fun x =>
    (⟨(x + θ x) / 2, hdec1 x⟩, ⟨(x - θ x) / (2 * d), hdec2 x⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    change s + t * d = s' + t' * d at h
    have h' := congrArg θ h
    rw [map_add, map_add, map_mul, map_mul, hs, ht, hs', ht', hθd] at h'
    have hss : s = s' := mul_left_cancel₀ h2 (by linear_combination h + h')
    have htt : t = t' := mul_right_cancel₀ hd0 (by linear_combination h - hss)
    subst hss
    subst htt
    rfl
  have hg : Function.Injective g := by
    intro x y h
    have h1 := congrArg (fun p => (p.1 : K)) h
    have h3 := congrArg (fun p => (p.2 : K)) h
    change (x + θ x) / 2 = (y + θ y) / 2 at h1
    change (x - θ x) / (2 * d) = (y - θ y) / (2 * d) at h3
    have e1 : x + θ x = y + θ y := by
      have h4 := congrArg (· * 2) h1
      simpa only [div_mul_cancel₀ _ h2] using h4
    have e2 : x - θ x = y - θ y := by
      have h4 := congrArg (· * (2 * d)) h3
      simpa only [div_mul_cancel₀ _ (mul_ne_zero h2 hd0)] using h4
    exact mul_left_cancel₀ h2 (by linear_combination e1 + e2)
  have h1 := Nat.card_le_card_of_injective f hf
  have h3 := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod] at h1 h3
  rw [sq]
  exact le_antisymm h1 h3

theorem apply_eq_self_of_odd_degree [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card K = p ^ f) (hf : Odd f) (θ : K →+* K) (hθ : ∀ x, θ (θ x) = x) (x : K) :
    θ x = x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have : CharP K p := charP_of_card_eq_prime_pow hKF
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  by_contra hx
  have h1 := card_fix_sq_of_two_ne_zero h2 θ hθ hx
  rw [hcard] at h1
  have hd : Nat.card {y : K // θ y = y} ∣ p ^ f :=
    ⟨Nat.card {y : K // θ y = y}, by rw [← h1, sq]⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [hj, ← pow_mul] at h1
  have h3 := Nat.pow_right_injective hp.two_le h1
  obtain ⟨k, hk⟩ := hf
  omega

end Field

theorem odd_of_pow_mod_eight {p f : ℕ} (hp : Odd p) (h : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) :
    Odd f := by
  by_contra hf
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.mp hf
  have hn : Odd (p ^ k) := hp.pow
  rw [show p ^ (k + k) = (p ^ k) ^ 2 by ring, Nat.pow_mod] at h
  generalize p ^ k = n at h hn
  have hodd : n % 2 = 1 := Nat.odd_iff.mp hn
  rcases (by omega : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7) with h8 | h8 | h8 | h8 <;>
    rw [h8] at h <;> norm_num at h

theorem card_le_four_of_sq_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hp2 : p ≠ 2) (hf : Odd f) (h3 : 3 < Nat.card K)
    (A : Subgroup (MulAut (PSL2 K))) (hA : ∀ α ∈ A, α * α = 1) : Nat.card A ≤ 4 := by
  classical
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp.out, hpodd, by obtain ⟨k, hk⟩ := hf; omega, hKcard⟩
  have hinj := pGammaL2ToMulAutPSL2_injective K hK h3
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hK h3
  set ρ := pGammaL2ToMulAutPSL2 K hK h3 with hρ
  set B := A.comap ρ with hBdef
  have hBA : Nat.card B = Nat.card A := by
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj A,
      Subgroup.card_map_of_injective hinj]
  have hB : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    apply hinj
    rw [map_mul, map_one]
    exact hA _ hx
  have hBr : ∀ x ∈ B, x.right = 1 := by
    intro x hx
    have h := congrArg SemidirectProduct.right (hB x hx)
    rw [SemidirectProduct.mul_right, SemidirectProduct.one_right] at h
    have hθ : ∀ y, x.right.toRingHom (x.right.toRingHom y) = y := fun y => by
      have h' := congrArg (fun σ : K ≃+* K => σ y) h
      simpa using h'
    apply RingEquiv.ext
    intro k
    exact apply_eq_self_of_odd_degree hp.out hp2 hKcard hf x.right.toRingHom hθ k
  set B' := B.comap (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) with hB'def
  have hB'B : Nat.card B' = Nat.card B := by
    have hmap : B'.map (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) = B := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        refine ⟨x.left, ?_, (AschbacherKnownGroup.FactsL2.eq_inl_of_right_eq_one (hBr x hx)).symm⟩
        change SemidirectProduct.inl x.left ∈ B
        rw [← AschbacherKnownGroup.FactsL2.eq_inl_of_right_eq_one (hBr x hx)]
        exact hx
    rw [← hmap, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  have hB' : ∀ y ∈ B', y * y = 1 := by
    intro y hy
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
    rw [map_mul, map_one]
    exact hB _ hy
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hp2B : IsPGroup 2 B' := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]
    exact hB' _ y.2)⟩
  obtain ⟨S, hS⟩ := hp2B.exists_le_sylow
  obtain ⟨m, hm, ⟨eS⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK S
  have hW := CFSG.QuasithinUnique.dihedral_card_le_four hm
    ((B'.subgroupOf (S : Subgroup (PGL2 K))).map eS.toMonoidHom) (by
      rintro _ ⟨w, hw, rfl⟩
      have hw' : ((w : PGL2 K)) ∈ B' := hw
      have hw2 : w ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, sq, Subgroup.coe_one]
        exact hB' _ hw')
      have h' : eS.toMonoidHom (w ^ 2) = 1 := by rw [hw2, map_one]
      rwa [map_pow] at h')
  rw [CFSG.QuasithinUnique.natCard_map_subgroupOf hS eS] at hW
  rw [← hBA, ← hB'B]
  exact hW

theorem nontrivial_psl2 {K : Type} [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    Nontrivial (PSL2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (PSL2 K)))
  obtain ⟨m, -, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hK S
  have : Nontrivial (S : Subgroup (PSL2 K)) := eS.toEquiv.nontrivial
  exact (Subtype.val_injective (p := fun x => x ∈ (S : Subgroup (PSL2 K)))).nontrivial

section Sylow

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

theorem exists_dihedral_model (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (Q : Sylow 2 G) : ∃ m : ℕ, 1 ≤ m ∧ ∃ ι : DihedralGroup (2 ^ m) →* G,
      Function.Injective ι ∧ ∀ d, ι d ∈ (Q : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Sylow 2 (PSL2 K) := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨m, hm, ⟨eQ⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hK Q'
  refine ⟨m, hm, (e.symm.toMonoidHom.comp (Q' : Subgroup (PSL2 K)).subtype).comp
    eQ.symm.toMonoidHom, ?_, ?_⟩
  · intro d d' h
    apply eQ.symm.injective
    apply Subtype.ext
    exact e.symm.injective h
  · intro d
    have hQ' : (Q' : Subgroup (PSL2 K)) = (Q : Subgroup G).map e.toMonoidHom :=
      Sylow.coe_mapSurjective e.surjective Q
    have h : ((eQ.symm d : Q') : PSL2 K) ∈ (Q : Subgroup G).map e.toMonoidHom := by
      rw [← hQ']
      exact (eQ.symm d).2
    obtain ⟨x, hx, hxe⟩ := h
    change e.symm ((eQ.symm d : Q') : PSL2 K) ∈ (Q : Subgroup G)
    rw [← hxe]
    change e.symm (e x) ∈ (Q : Subgroup G)
    rw [MulEquiv.symm_apply_apply]
    exact hx

theorem four_le_card_omegaOne (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K)
    (Q : Sylow 2 G) : 4 ≤ Nat.card (omegaOne (Q : Subgroup G)) := by
  classical
  obtain ⟨m, hm, ι, hι, hιQ⟩ := exists_dihedral_model hK e Q
  have : Fact (1 < 2 ^ m) := ⟨Nat.one_lt_two_pow (by omega)⟩
  have hsr : ∀ i : ZMod (2 ^ m), ι (DihedralGroup.sr i) ^ 2 = 1 := fun i => by
    rw [← map_pow, sq, DihedralGroup.sr_mul_self, map_one]
  have hne1 : ∀ i : ZMod (2 ^ m), ι (DihedralGroup.sr i) ≠ 1 := by
    intro i h
    rw [← map_one ι] at h
    have h' := hι h
    rw [DihedralGroup.one_def] at h'
    cases h'
  have hne01 : ι (DihedralGroup.sr 0) ≠ ι (DihedralGroup.sr 1) := by
    intro h
    have h' := hι h
    rw [DihedralGroup.sr.injEq] at h'
    exact zero_ne_one h'
  have hsub : ({1, ι (DihedralGroup.sr 0), ι (DihedralGroup.sr 1)} : Set G) ⊆
      (omegaOne (Q : Subgroup G) : Set G) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact (omegaOne _).one_mem
    · exact mem_omegaOne (hιQ _) (hsr 0)
    · exact mem_omegaOne (hιQ _) (hsr 1)
  have h3 : ({1, ι (DihedralGroup.sr 0), ι (DihedralGroup.sr 1)} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_, _, _, (hne1 0).symm, (hne1 1).symm, hne01, rfl⟩
  have hcard_eq : Nat.card (omegaOne (Q : Subgroup G)) =
      ((omegaOne (Q : Subgroup G) : Set G)).ncard := Nat.card_coe_set_eq _
  have hle : 3 ≤ Nat.card (omegaOne (Q : Subgroup G)) := by
    rw [← h3, hcard_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hp : IsPGroup 2 (omegaOne (Q : Subgroup G)) := Q.isPGroup'.to_le (omegaOne_le _)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rw [hn] at hle ⊢
  rcases n with _ | _ | n
  · norm_num at hle
  · norm_num at hle
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Sylow

theorem le_iSup_centralizer_of_psl2 {Y : Type} [Group Y] [Finite Y] {X P : Subgroup Y}
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hq : 11 ≤ Nat.card K) (e : ↥X ≃* PSL2 K)
    (hP : IsSylowOf 2 P X) :
    X ≤ ⨆ z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1}, X ⊓ Subgroup.centralizer {(z : Y)} := by
  classical
  obtain ⟨Q, hQ⟩ := hP
  set M := ⨆ z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1}, X ⊓ Subgroup.centralizer {(z : Y)}
    with hM
  obtain ⟨m, hm, ι, hι, hιQ⟩ := exists_dihedral_model hK e Q
  set k : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) with hk
  have hk0 : k ≠ 0 := by
    intro h
    rw [hk, ZMod.natCast_eq_zero_iff] at h
    have h2 := Nat.le_of_dvd (by positivity) h
    have : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hkk : k + k = 0 := by
    have h1 : k + k = ((2 ^ m : ℕ) : ZMod (2 ^ m)) := by
      rw [hk, ← Nat.cast_add]
      congr 1
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    rw [h1, ZMod.natCast_self]
  set t₁ : X := ι (DihedralGroup.sr 0) with ht₁
  set t₂ : X := ι (DihedralGroup.r k) with ht₂
  have h₁ : t₁ ^ 2 = 1 := by rw [ht₁, ← map_pow, sq, DihedralGroup.sr_mul_self, map_one]
  have h₂ : t₂ ^ 2 = 1 := by
    rw [ht₂, ← map_pow, sq, DihedralGroup.r_mul_r, hkk, ← DihedralGroup.one_def, map_one]
  have h₁' : t₁ ≠ 1 := by
    intro h
    rw [ht₁, ← map_one ι] at h
    have h' := hι h
    rw [DihedralGroup.one_def] at h'
    cases h'
  have h₂' : t₂ ≠ 1 := by
    intro h
    rw [ht₂, ← map_one ι] at h
    have h' := hι h
    rw [DihedralGroup.one_def, DihedralGroup.r.injEq] at h'
    exact hk0 h'
  have hne : t₁ ≠ t₂ := by
    intro h
    have h' := hι h
    cases h'
  have hc : t₁ * t₂ = t₂ * t₁ := by
    rw [ht₁, ht₂, ← map_mul, ← map_mul, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 2
    linear_combination hkk
  have hcent : ∀ t : X, t ∈ Q → t ^ 2 = 1 → t ≠ 1 → ∀ y : X, Commute y t → (y : Y) ∈ M := by
    intro t htQ ht2 ht1 y hyt
    have hzP : (t : Y) ∈ P := (coe_mem_iff hQ).mpr htQ
    have hz2 : (t : Y) ^ 2 = 1 := by rw [← Subgroup.coe_pow, ht2, Subgroup.coe_one]
    have hz1 : (t : Y) ≠ 1 := fun h => ht1 (Subtype.ext h)
    apply (le_iSup (fun z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1} =>
      X ⊓ Subgroup.centralizer {(z : Y)}) ⟨(t : Y), hzP, hz2, hz1⟩)
    have h := congrArg Subtype.val hyt.eq
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
  have hH := AschbacherKnownGroup.FactsL2.case_one_psl2 hKcard hK hq (t₁ := e t₁) (t₂ := e t₂)
    (by rw [← map_pow, h₁, map_one]) (by rw [← map_pow, h₂, map_one])
    (fun h => h₁' (e.injective (h.trans (map_one e).symm)))
    (fun h => h₂' (e.injective (h.trans (map_one e).symm)))
    (fun h => hne (e.injective h)) (by rw [← map_mul, hc, map_mul])
    ((M.subgroupOf X).map e.toMonoidHom)
    (fun y hy => ⟨e.symm y, by
      show ((e.symm y : X) : Y) ∈ M
      apply hcent t₁ (hιQ _) h₁ h₁'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc' : Commute y (e t₁) := by rw [← hn]; exact Commute.self_zpow y n
      have hc'' := hc'.map e.symm.toMonoidHom
      simpa using hc'', by simp⟩)
    (fun y hy => ⟨e.symm y, by
      show ((e.symm y : X) : Y) ∈ M
      apply hcent t₂ (hιQ _) h₂ h₂'
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hc' : Commute y (e t₂) := by rw [← hn]; exact Commute.self_zpow y n
      have hc'' := hc'.map e.symm.toMonoidHom
      simpa using hc'', by simp⟩)
  intro x hx
  have h := hH ▸ Subgroup.mem_top (e ⟨x, hx⟩)
  obtain ⟨x', hx', hxe⟩ := h
  have hx'x : x' = ⟨x, hx⟩ := e.injective hxe
  rw [hx'x] at hx'
  exact hx'

theorem nonempty_mulEquiv_psl2_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nonempty (PSL(2, K) ≃* PSL(2, GaloisField 2 2)) := by
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr hK)
  have h4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e4⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl h4)
  exact ⟨((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).trans
    e5).trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 2)).trans e4).symm⟩

end Goldschmidt

end CFSG.ComponentClassification.AschbacherToolkit
