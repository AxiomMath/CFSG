module

public import CFSG.GH74.GLS.Stage4.T2RemProofSetup
public import CFSG.GH74.GLS.Stage4.T2RemProofShape
public import CFSG.GH74.GLS.Stage4.T2RemProofExp
public import CFSG.GH74.GLS.Stage4.T2CentS
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.BNPair CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel CFSG.Blueprint
  CFSG.GH74.GLS.Stage4.Rest.Rem.Shape

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

section Gen

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem C1_le_normalizer (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
  fun c hc => Subgroup.mem_normalizer_fintype (fun k hk =>
    conj_mem_of_relIndex_two hSet.le_residual hSet.index_two c hc k hk)

theorem K_le_normalizer₁ (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) :=
  fun k hk => Subgroup.mem_normalizer_fintype (fun x hx => t2C_K₁_normal_K hSet.comm k hk x hx)

theorem K_le_normalizer₂ (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) :=
  fun k hk => Subgroup.mem_normalizer_fintype (fun x hx => t2C_K₂_normal_K hSet.comm k hk x hx)

theorem isSylowOf_C1' {S : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hSidx : ¬ 2 ∣ S.index)
    (hSz : ∀ s ∈ S, s * z = z * s) :
    IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := le_oPrimeResidualOf_centralizer hS2 hSz
  exact (isSylowOf_iff).2 ⟨hle, hS2, fun h => hSidx (h.trans (Subgroup.relIndex_dvd_index_of_le hle))⟩

theorem exists_sylow_ge (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {W : Subgroup G}
    (hW : IsPGroup 2 ↥W) (hWC : W ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))) :
    ∃ S : Subgroup G, IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G))) ∧ W ≤ S := by
  have hWz : ∀ a ∈ W, a * z = z * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1
      ((Subgroup.map_subtype_le _ : oPrimeResidualOf 2 (centralizer ({z} : Set G)) ≤
        centralizer ({z} : Set G)) (hWC ha))
  obtain ⟨S, hS2, hSidx, hWS, hSz⟩ := exists_sylow_two_contains hSet.central W hW hWz
  exact ⟨S, isSylowOf_C1' hS2 hSidx hSz, hWS⟩

theorem sylow_inf_K_isSylowOf (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G)))) :
    IsSylowOf 2 (S ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.inf_of_le_normalizer hSet.le_residual (C1_le_normalizer hSet)

theorem sylow_inf_K₁_isSylowOf (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G)))) :
    IsSylowOf 2 ((S ⊓ (K₁ ⊔ K₂)) ⊓ K₁) K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (sylow_inf_K_isSylowOf hSet hS).inf_of_le_normalizer le_sup_left (K_le_normalizer₁ hSet)

theorem sylow_inf_K₂_isSylowOf (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G)))) :
    IsSylowOf 2 ((S ⊓ (K₁ ⊔ K₂)) ⊓ K₂) K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (sylow_inf_K_isSylowOf hSet hS).inf_of_le_normalizer le_sup_right (K_le_normalizer₂ hSet)

theorem central_inf_K (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {S : Subgroup G}
    (hS : IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G)))) :
    ∀ x ∈ S ⊓ (K₁ ⊔ K₂), (∀ w ∈ S ⊓ (K₁ ⊔ K₂), x * w = w * x) → x ∈ Subgroup.zpowers z := by
  intro x hxN hxc
  have := hSet.finite₁
  have := hSet.finite₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  obtain ⟨hP₁, -, hs₁⟩ := (isSylowOf_iff).1 (sylow_inf_K₁_isSylowOf hSet hS)
  obtain ⟨hP₂, -, hs₂⟩ := (isSylowOf_iff).1 (sylow_inf_K₂_isSylowOf hSet hS)
  obtain ⟨-, hP₁', hs₁'⟩ := (isSylowOf_iff).1 (sylow_inf_K₁_isSylowOf hSet hS)
  obtain ⟨-, hP₂', hs₂'⟩ := (isSylowOf_iff).1 (sylow_inf_K₂_isSylowOf hSet hS)
  obtain ⟨a, ha, b, hb, hxab⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hxN.2
  have ha1 : a ∈ Subgroup.zpowers z := by
    refine t2C_cent_sylow_K hodd₁ e₁ hP₁' hs₁' hSet.z_mem₁ hze₁ a ha (fun p hp => ?_)
    have h1 := hxc p hp.1
    have h2 : b * p = p * b := (hSet.comm p hp.2 b hb).symm
    rw [hxab] at h1
    have : a * p * b = p * a * b := by
      calc a * p * b = a * (p * b) := by group
        _ = a * (b * p) := by rw [h2]
        _ = a * b * p := by group
        _ = p * (a * b) := h1
        _ = p * a * b := by group
    exact mul_right_cancel this
  have hb1 : b ∈ Subgroup.zpowers z := by
    refine t2C_cent_sylow_K hodd₂ e₂ hP₂' hs₂' hSet.z_mem₂ hze₂ b hb (fun p hp => ?_)
    have h1 := hxc p hp.1
    have h2 : a * p = p * a := hSet.comm a ha p hp.2
    rw [hxab] at h1
    have : a * (b * p) = a * (p * b) := by
      calc a * (b * p) = a * b * p := by group
        _ = p * (a * b) := h1
        _ = (p * a) * b := by group
        _ = (a * p) * b := by rw [h2]
        _ = a * (p * b) := by group
    exact mul_left_cancel this
  rw [hxab]
  exact Subgroup.mul_mem _ ha1 hb1

omit [Finite G] in
theorem exp_of_two_elt (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {n : ℕ} (hn : 2 ≤ n)
    (hv₁ : (Nat.card ↥K₁).factorization 2 = n + 1) (hv₂ : (Nat.card ↥K₂).factorization 2 = n + 1)
    {x : G} (hxK : x ∈ K₁ ⊔ K₂) {m : ℕ} (hxm : x ^ (2 ^ m) = 1) : x ^ (2 ^ n) = 1 := by
  have := hSet.finite₁
  have := hSet.finite₂
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  obtain ⟨e₁⟩ := hSet.iso₁
  obtain ⟨e₂⟩ := hSet.iso₂
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hxK
  have hab : Commute a b := hSet.comm a ha b hb
  have h1 : a ^ (2 ^ m) * b ^ (2 ^ m) = 1 := by rw [← hab.mul_pow]; exact hxm
  have hzz := t2C_zz hSet
  have hsq : ∀ g ∈ K₁ ⊓ K₂, g * g = 1 := by
    intro g hg
    rw [hSet.inter_eq] at hg
    rcases t2C_zpowers_cases hzz hg with h | h
    · rw [h, one_mul]
    · rw [h]; exact hzz
  have ha2 : a ^ (2 ^ (m + 1)) = 1 := by
    have hmem : a ^ (2 ^ m) ∈ K₁ ⊓ K₂ := by
      refine ⟨pow_mem ha _, ?_⟩
      have : a ^ (2 ^ m) = (b ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact K₂.inv_mem (pow_mem hb _)
    rw [pow_succ, pow_mul, pow_two]
    exact hsq _ hmem
  have hb2 : b ^ (2 ^ (m + 1)) = 1 := by
    have hmem : b ^ (2 ^ m) ∈ K₁ ⊓ K₂ := by
      refine ⟨?_, pow_mem hb _⟩
      have : b ^ (2 ^ m) = (a ^ (2 ^ m))⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact K₁.inv_mem (pow_mem ha _)
    rw [pow_succ, pow_mul, pow_two]
    exact hsq _ hmem
  rw [hab.mul_pow, pow_two_pow_eq_one_of_sl2 hodd₁ e₁ hn hv₁ ha ha2,
    pow_two_pow_eq_one_of_sl2 hodd₂ e₂ hn hv₂ hb hb2, mul_one]


end Gen

section Main


variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_shape_equiv
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) :
    ∃ n : ℕ, 2 ≤ n ∧ (Nat.card ↥K₁).factorization 2 = n + 1 ∧ (Nat.card ↥K₂).factorization 2 = n + 1 ∧
      ∀ S : Subgroup G, IsSylowOf 2 S (oPrimeResidualOf 2 (centralizer ({z} : Set G))) →
        Nonempty (ShapeGrp n ≃* ↥S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, S₀, S', A, a, t, y, hn, hSyl, hzS, hSz, ⟨φ⟩, hsc, hv₁, hv₂⟩ := exists_data hSet
  obtain ⟨Ψ⟩ := hsc.nonempty_mulEquiv_shapeGrp
  refine ⟨n, hn, hv₁, hv₂, fun S hS => ?_⟩
  obtain ⟨k, -, hk⟩ := hSyl.exists_mem_conj hS
  obtain ⟨χ⟩ := nonempty_equiv_of_conj hk
  exact ⟨(Ψ.trans φ.symm).trans χ.symm⟩

theorem lemmaL (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) {t : G} (htt : t * t = 1)
    (htK : t ∉ K₁ ⊔ K₂) (W : Subgroup G) (hW : IsPGroup 2 ↥W)
    (hWC : W ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))) (htW : t ∈ W) :
    ∃ U : Finset G, U.card ≤ 4 ∧ (∀ y ∈ U, y * y = 1) ∧
      ∀ x ∈ W, x ∈ K₁ ⊔ K₂ → x * t = t * x → x ∈ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hv₁, hv₂, hshape⟩ := exists_shape_equiv hSet
  obtain ⟨S, hS, hWS⟩ := exists_sylow_ge hSet hW hWC
  obtain ⟨Ψ⟩ := hshape S hS
  set N : Subgroup ↥S := (S ⊓ (K₁ ⊔ K₂)).subgroupOf S with hN
  have hNidx : N.index = 2 := sylow_inf_K hSet hS
  have hmemN : ∀ x : ↥S, x ∈ N ↔ (x : G) ∈ K₁ ⊔ K₂ := by
    intro x
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hexp : ∀ x ∈ N, x ^ (2 ^ n) = 1 := by
    intro x hx
    obtain ⟨m, hm⟩ := hS.isPGroup x
    apply Subtype.ext
    have hxm : (x : G) ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    simpa using exp_of_two_elt hSet hn hv₁ hv₂ ((hmemN x).1 hx) hxm
  have hZ : ∀ x ∈ N, (∀ w ∈ N, x * w = w * x) → ∀ x' ∈ N, (∀ w ∈ N, x' * w = w * x') →
      x = 1 ∨ x' = 1 ∨ x = x' := by
    intro x hx hcx x' hx' hcx'
    have key : ∀ y ∈ N, (∀ w ∈ N, y * w = w * y) → (y : G) ∈ Subgroup.zpowers z := by
      intro y hy hcy
      refine central_inf_K hSet hS (y : G) ⟨y.2, (hmemN y).1 hy⟩ (fun w hw => ?_)
      have := hcy ⟨w, hw.1⟩ ((hmemN _).2 hw.2)
      simpa using congrArg Subtype.val this
    have hzz := t2C_zz hSet
    rcases t2C_zpowers_cases hzz (key x hx hcx) with h | h <;>
      rcases t2C_zpowers_cases hzz (key x' hx' hcx') with h' | h'
    · exact Or.inl (Subtype.ext h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h'))
    · exact Or.inr (Or.inr (Subtype.ext (h.trans h'.symm)))
  let s : ↥S := ⟨t, hWS htW⟩
  have hs : s ∉ N := fun h => htK ((hmemN s).1 h)
  have hs2 : s * s = 1 := Subtype.ext (by simpa using htt)
  obtain ⟨U', hcard, hsq, hmem⟩ := centralizer_outside_iso Ψ hn N hNidx hexp hZ s hs hs2
  refine ⟨U'.map ⟨Subtype.val, Subtype.val_injective⟩, by simpa using hcard, ?_, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
    simpa using congrArg Subtype.val (hsq y' hy')
  · intro x hxW hxK hxt
    refine Finset.mem_map.2 ⟨⟨x, hWS hxW⟩, hmem ⟨x, hWS hxW⟩ ((hmemN _).2 hxK) ?_, rfl⟩
    exact Subtype.ext (by simpa using hxt)

end Main

end CFSG.GH74.GLS.Stage4.Rest.Rem
