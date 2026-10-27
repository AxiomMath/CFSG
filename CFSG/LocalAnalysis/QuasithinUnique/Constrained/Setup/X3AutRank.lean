module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutBridge
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.QuasithinUnique.Setup.X3Aut

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def ConjInto (n : AutA6) (B : Subgroup AutA6) (E : List (List ℕ)) : Prop :=
  ∀ x ∈ B, cd (n * x * n⁻¹) ∈ E

theorem conjInto_surj {n : AutA6} {B : Subgroup AutA6} {E : List (List ℕ)} (hnd : E.Nodup)
    (hcard : Nat.card B = E.length) (h : ConjInto n B E) :
    ∀ e ∈ E, ∃ b ∈ B, cd (n * b * n⁻¹) = e := by
  classical
  let f : AutA6 → List ℕ := fun x => cd (n * x * n⁻¹)
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 := cd_injective hxy
    have h2 : n * x = n * y := mul_right_cancel h1
    exact mul_left_cancel h2
  have himg : f '' (B : Set AutA6) ⊆ (E.toFinset : Set (List ℕ)) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using h x hx
  have hcard1 : (f '' (B : Set AutA6)).ncard = Nat.card B := by
    rw [Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
    rfl
  have hcard2 : (E.toFinset : Set (List ℕ)).ncard = E.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  have heq : f '' (B : Set AutA6) = (E.toFinset : Set (List ℕ)) :=
    Set.eq_of_subset_of_ncard_le himg (by rw [hcard1, hcard2, hcard]) (Set.toFinite _)
  intro e he
  have : e ∈ (E.toFinset : Set (List ℕ)) := by simpa using he
  rw [← heq] at this
  obtain ⟨b, hb, hbe⟩ := this
  exact ⟨b, hb, hbe⟩

theorem isElementaryAbelian_of_le' {A B : Subgroup AutA6} [hA : CFSG.IsElementaryAbelian 2 ↥A]
    (h : B ≤ A) : CFSG.IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.of_le inferInstance h

theorem exists_hyperplane {A : Subgroup AutA6} (hel : CFSG.IsElementaryAbelian 2 ↥A) {r : ℕ}
    (hcard : Nat.card A = 2 ^ (r + 1)) :
    ∃ a ∈ A, a * a = 1 ∧ ∃ B : Subgroup AutA6, B ≤ A ∧ CFSG.IsElementaryAbelian 2 ↥B ∧
      Nat.card B = 2 ^ r ∧ a ∉ B ∧ ∀ x ∈ A, x ∈ B ∨ a * x ∈ B := by
  have := hel
  have hne : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [hbot, Subgroup.card_bot] at hcard
    have : 2 ≤ 2 ^ (r + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a, ha, ha1⟩ := hne
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
  let a₀ : ↥A := ⟨a, ha⟩
  have ha₀2 : a₀ ^ 2 = 1 := Subtype.ext ha2
  have ha₀1 : a₀ ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 ↥A (Subgroup.zpowers a₀)
  have hcomp : Subgroup.IsComplement' (Subgroup.zpowers a₀) C := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hC.disjoint
    have := Subgroup.mul_normal (Subgroup.zpowers a₀) C
    rw [← this, hC.sup_eq_top]
    rfl
  have hprod := hcomp.card_mul_card
  have hord : Nat.card (Subgroup.zpowers a₀) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha₀2 ha₀1
  have hCcard : Nat.card C = 2 ^ r := by
    rw [hord, hcard] at hprod
    rw [pow_succ] at hprod
    omega
  refine ⟨a, ha, by rw [← sq]; exact ha2, C.map A.subtype, Subgroup.map_subtype_le C,
    isElementaryAbelian_of_le' (A := A) (Subgroup.map_subtype_le C), ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hCcard]
  · rintro ⟨c, hc, hca⟩
    have hc' : c = a₀ := Subtype.ext hca
    have hca0 : a₀ ∈ C := hc' ▸ hc
    exact ha₀1 (Subgroup.disjoint_def.mp hC.disjoint (Subgroup.mem_zpowers a₀) hca0)
  · intro x hx
    have hx0 : (⟨x, hx⟩ : ↥A) ∈ Subgroup.zpowers a₀ ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx0
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hord2 : orderOf a₀ = 2 := orderOf_eq_prime ha₀2 ha₀1
    have hk : a₀ ^ k = 1 ∨ a₀ ^ k = a₀ := by
      rw [← zpow_mod_orderOf, hord2]
      have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
      rcases this with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
    have haa : a * a = 1 := by rw [← sq]; exact ha2
    rcases hk with hk | hk
    · left
      rw [hk, one_mul] at hyz
      exact ⟨z, hz, congrArg Subtype.val hyz⟩
    · right
      rw [hk] at hyz
      refine ⟨z, hz, ?_⟩
      have hx' : a * (z : AutA6) = x := congrArg Subtype.val hyz
      show (z : AutA6) = a * x
      rw [← hx', ← mul_assoc, haa, one_mul]


theorem rank_lemma : ∀ r : ℕ, ∀ A : Subgroup AutA6, CFSG.IsElementaryAbelian 2 ↥A →
    Nat.card A = 2 ^ r → r ≤ 3 ∧ ∃ j, j < repsC.length ∧ (rep j).length = 2 ^ r ∧
      ∃ n : AutA6, ConjInto n A (rep j) := by
  intro r
  induction r with
  | zero =>
    intro A hA hcard
    have hbot : A = ⊥ := by
      rw [← Subgroup.card_eq_one]; simpa using hcard
    have h0 : 0 < repsC.length := by
      by_contra h
      have h1 : rep 0 = [] := by unfold rep; exact List.getD_eq_default _ _ (by omega)
      rw [rep_zero] at h1
      simp at h1
    refine ⟨by omega, 0, h0, ?_, 1, ?_⟩
    · rw [rep_zero]; rfl
    · intro x hx
      rw [hbot, Subgroup.mem_bot] at hx
      subst hx
      rw [rep_zero]
      simp [cd_one]
  | succ r ih =>
    intro A hA hcard
    have := hA
    obtain ⟨a, haA, haa, B, hBA, hBel, hBcard, haB, hAB⟩ := exists_hyperplane hA hcard
    obtain ⟨hr3, j, hj, hjlen, n, hn⟩ := ih B hBel hBcard
    obtain ⟨hnd, hid, hlen', hinv, hclos, hrk⟩ := rep_spec hj
    have hsurj := conjInto_surj hnd (by rw [hBcard, hjlen]) hn
    have hcomm_AB : ∀ b ∈ B, a * b = b * a := fun b hb => setLike_mul_comm (s := A) haA (hBA hb)
    have ha1 : a ≠ 1 := fun h => haB (h ▸ B.one_mem)
    obtain ⟨c, hc⟩ : ∃ c : AutA6, c = n * a * n⁻¹ := ⟨_, rfl⟩
    have hcc : c * c = 1 := by
      calc c * c = n * (a * a) * n⁻¹ := by rw [hc]; group
        _ = 1 := by rw [haa]; group
    have hcmem : cd c ∈ invsC := by
      rw [mem_invsC_iff]
      refine ⟨cd_mem_autL c, ?_, ?_⟩
      · rw [← cd_mul, hcc, cd_one]
      · intro h
        have h1 : c = 1 := cd_injective (h.trans cd_one.symm)
        apply ha1
        have h2 : n * a * n⁻¹ = n * 1 * n⁻¹ := by rw [← hc, h1]; group
        have h3 : a = 1 := by
          have := mul_right_cancel h2
          exact mul_left_cancel (this.trans (mul_one n))
        exact h3
    have hcnot : cd c ∉ rep j := by
      intro hmem
      obtain ⟨b, hb, hbe⟩ := hsurj _ hmem
      have h1 : n * b * n⁻¹ = c := cd_injective hbe
      have h2 : n * b * n⁻¹ = n * a * n⁻¹ := h1.trans hc
      have hb' : b = a := mul_left_cancel (mul_right_cancel h2)
      exact haB (hb' ▸ hb)
    have hccomm : ∀ e ∈ rep j, Core.cmul (cd c) e = Core.cmul e (cd c) := by
      intro e he
      obtain ⟨b, hb, rfl⟩ := hsurj e he
      rw [← cd_mul, ← cd_mul]
      congr 1
      calc c * (n * b * n⁻¹) = n * (a * b) * n⁻¹ := by rw [hc]; group
        _ = n * (b * a) * n⁻¹ := by rw [hcomm_AB b hb]
        _ = n * b * n⁻¹ * c := by rw [hc]; group
    have hkey : (j, cd c) ∈ keysC := mem_keysC_of hj hcmem hcnot hccomm
    obtain ⟨hlt8, i, k, hk, hall, hklen⟩ := step_spec hkey
    obtain ⟨n', hn'⟩ := exists_cd_getD i
    have hr3' : r + 1 ≤ 3 := by
      have h8 : 2 ^ r < 8 := hjlen ▸ hlt8
      by_contra hcon
      have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨hndk, hidk, hlenk', hinvk, hclosk, hrkk⟩ := rep_spec hk
    have himg : ∀ y : AutA6, cd y ∈ rep j ++ [cd c] → cd (n' * y * n'⁻¹) ∈ rep k := by
      intro y hy
      have h1 := hall (cd y) hy
      rw [← hn', ← cd_inv, ← cd_mul, ← cd_mul] at h1
      exact h1
    refine ⟨hr3', k, hk, ?_, n' * n, ?_⟩
    · rw [hklen, hjlen]; ring
    · intro x hx
      rcases hAB x hx with hxB | haxB
      · have h1 : cd (n * x * n⁻¹) ∈ rep j := hn x hxB
        have h2 := himg (n * x * n⁻¹) (List.mem_append_left _ h1)
        have : (n' * n) * x * (n' * n)⁻¹ = n' * (n * x * n⁻¹) * n'⁻¹ := by group
        rw [this]; exact h2
      · have h1 : cd (n * (a * x) * n⁻¹) ∈ rep j := hn _ haxB
        have h2 := himg (n * (a * x) * n⁻¹) (List.mem_append_left _ h1)
        have h3 := himg c (List.mem_append_right _ (List.mem_singleton_self _))
        have hx' : x = a * (a * x) := by rw [← mul_assoc, haa, one_mul]
        have hxeq : (n' * n) * x * (n' * n)⁻¹ =
            (n' * c * n'⁻¹) * (n' * (n * (a * x) * n⁻¹) * n'⁻¹) := by
          calc (n' * n) * x * (n' * n)⁻¹ = n' * (n * (a * (a * x)) * n⁻¹) * n'⁻¹ := by
                rw [← hx']; group
            _ = _ := by rw [hc]; group
        rw [hxeq, cd_mul]
        exact (hclosk _ h3 _ h2).2

end CFSG.QuasithinUnique.Setup.X3Aut
