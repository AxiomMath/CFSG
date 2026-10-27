module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L4

public section

namespace CFSG.EvenSporadicStandard.Fin76b

section Centre

theorem four_mem_center_aut {Q : Type} [Group Q] (σ : Q ≃* Q) {z : Q}
    (hz : z ∈ Subgroup.center Q) : σ z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h1 := congrArg σ (hz (σ.symm g))
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  exact h1

theorem four_normal_of_le_center {Q : Type} [Group Q] {N : Subgroup Q}
    (h : N ≤ Subgroup.center Q) : N.Normal :=
  ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.mp (h hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩

@[expose] def fourFix {G : Type} [Group G] (e : G ≃* G) : Subgroup G where
  carrier := {y | e y = y}
  mul_mem' := fun {a b} (ha : e a = a) (hb : e b = b) => by
    show e (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := by
    show e 1 = 1
    exact map_one e
  inv_mem' := fun {a} (ha : e a = a) => by
    show e a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem four_d_mul {Q : Type} [Group Q] (σ : Q ≃* Q) {x y : Q}
    (hx : (σ x)⁻¹ * x ∈ Subgroup.center Q) :
    (σ (x * y))⁻¹ * (x * y) = ((σ x)⁻¹ * x) * ((σ y)⁻¹ * y) := by
  have hc : (σ y)⁻¹ * ((σ x)⁻¹ * x) = ((σ x)⁻¹ * x) * (σ y)⁻¹ :=
    Subgroup.mem_center_iff.mp hx _
  rw [map_mul, mul_inv_rev]
  calc (σ y)⁻¹ * (σ x)⁻¹ * (x * y) = ((σ y)⁻¹ * ((σ x)⁻¹ * x)) * y := by group
    _ = (((σ x)⁻¹ * x) * (σ y)⁻¹) * y := by rw [hc]
    _ = (σ x)⁻¹ * x * ((σ y)⁻¹ * y) := by group

end Centre

section Involution

theorem four_exists_central_involution {Q F : Type} [Group Q] [Finite Q] [Group F] [Finite F]
    (hQ : IsPGroup 2 Q) (hF : IsPGroup 2 F) (hQ4 : 4 ≤ Nat.card Q) (φ : F →* MulAut Q) :
    ∃ w : Q, w ≠ 1 ∧ w * w = 1 ∧ (∀ g : Q, g * w = w * g) ∧ ∀ f : F, φ f w = w := by
  classical
  have : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  letI : MulAction F (Subgroup.center Q) :=
    { smul := fun f z => ⟨φ f (z : Q), four_mem_center_aut (φ f) z.2⟩
      one_smul := fun z => Subtype.ext (show φ 1 (z : Q) = z by simp)
      mul_smul := fun f g z => Subtype.ext (show φ (f * g) (z : Q) = φ f (φ g (z : Q)) by
        rw [map_mul, MulAut.mul_apply]) }
  have hZ : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
  have hcz : 1 < Nat.card (Subgroup.center Q) := by
    have := IsPGroup.center_nontrivial hQ
    exact Finite.one_lt_card
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZ
  have hodd : Nat.card (Subgroup.center Q) % 2 = 0 := by
    rcases n with _ | m
    · rw [hn] at hcz
      norm_num at hcz
    · rw [hn, pow_succ]
      omega
  obtain ⟨x, hx1, hxfix⟩ := exists_fixed_ne_of_even hF hodd (1 : Subgroup.center Q)
    (fun f => Subtype.ext (show φ f 1 = 1 by simp))
  have hxQ : (x : Q) ∈ Subgroup.center Q := x.2
  have hx1' : (x : Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hφx : ∀ f : F, φ f (x : Q) = (x : Q) := fun f => congrArg Subtype.val (hxfix f)
  have hex : ∃ k : ℕ, (x : Q) ^ 2 ^ k = 1 := hQ (x : Q)
  have hspec := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hspec
    exact hx1' hspec
  obtain ⟨n', hn'⟩ : ∃ n', Nat.find hex = n' + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hw1 : (x : Q) ^ 2 ^ n' ≠ 1 := Nat.find_min hex (by omega)
  have hw2 : (x : Q) ^ 2 ^ n' * (x : Q) ^ 2 ^ n' = 1 := by
    rw [← pow_add]
    have h2 : 2 ^ n' + 2 ^ n' = 2 ^ (n' + 1) := by
      rw [pow_succ]
      omega
    rw [h2, ← hn']
    exact hspec
  refine ⟨(x : Q) ^ 2 ^ n', hw1, hw2, ?_, ?_⟩
  · intro g
    exact Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hxQ _) g
  · intro f
    rw [map_pow, hφx f]

end Involution

section Quotient

@[expose] def fourInducedHom {Q F : Type} [Group Q] [Group F] (φ : F →* MulAut Q)
    (N : Subgroup Q) [N.Normal] (hstab : ∀ f : F, N.map (φ f : Q →* Q) = N) :
    F →* MulAut (Q ⧸ N) :=
  MonoidHom.mk' (fun f => QuotientGroup.congr N N (φ f) (hstab f)) (fun f g => by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H q =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply])

theorem four_card_fixed_quotient_le {Q : Type} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (hN2 : Nat.card N = 2) (hNc : N ≤ Subgroup.center Q) (σ : Q ≃* Q)
    (hσ : N.map (σ : Q →* Q) = N) :
    Nat.card {y : Q ⧸ N // QuotientGroup.congr N N σ hσ y = y} ≤
      Nat.card {q : Q // σ q = q} := by
  classical
  have hσN : ∀ n ∈ N, σ n ∈ N := by
    intro n hn
    have h1 : σ n ∈ N.map (σ : Q →* Q) := Subgroup.mem_map_of_mem _ hn
    rw [hσ] at h1
    exact h1
  obtain ⟨P, hP⟩ : ∃ P : Subgroup Q, ∀ x : Q, x ∈ P ↔ (σ x)⁻¹ * x ∈ N := by
    refine ⟨(fourFix (QuotientGroup.congr N N σ hσ)).comap (QuotientGroup.mk' N), fun x => ?_⟩
    rw [Subgroup.mem_comap]
    show QuotientGroup.congr N N σ hσ (x : Q ⧸ N) = (x : Q ⧸ N) ↔ _
    rw [QuotientGroup.congr_mk, QuotientGroup.eq]
  have hPN : ∀ p : P, (σ (p : Q))⁻¹ * (p : Q) ∈ N := fun p => (hP p).mp p.2
  have hPc : ∀ p : P, (σ (p : Q))⁻¹ * (p : Q) ∈ Subgroup.center Q := fun p => hNc (hPN p)
  obtain ⟨c, hc⟩ : ∃ c : P →* Q, ∀ p : P, c p = (σ (p : Q))⁻¹ * (p : Q) :=
    ⟨MonoidHom.mk' (fun p : P => (σ (p : Q))⁻¹ * (p : Q)) (fun p q => by
      show (σ ((p : Q) * (q : Q)))⁻¹ * ((p : Q) * (q : Q)) =
        ((σ (p : Q))⁻¹ * (p : Q)) * ((σ (q : Q))⁻¹ * (q : Q))
      exact four_d_mul σ (hPc p)), fun p => rfl⟩
  have hcN : c.range ≤ N := by
    intro y hy
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [hc p]
    exact hPN p
  have hrange2 : Nat.card c.range ≤ 2 := by
    have h := Subgroup.card_le_of_le hcN
    rwa [hN2] at h
  obtain ⟨K, hK⟩ : ∃ K : Subgroup Q, ∀ x : Q, x ∈ K ↔ σ x = x :=
    ⟨fourFix σ, fun x => Iff.rfl⟩
  have hkerc : c.ker.map P.subtype = K := by
    ext x
    rw [Subgroup.mem_map, hK]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 : (σ (p : Q))⁻¹ * (p : Q) = 1 := by
        rw [← hc p]
        exact hp
      exact inv_mul_eq_one.mp h1
    · intro hx
      have hxP : x ∈ P := (hP x).mpr (by
        rw [hx, inv_mul_cancel]
        exact N.one_mem)
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hc]
      show (σ x)⁻¹ * x = 1
      rw [hx, inv_mul_cancel]
  have hkerc_card : Nat.card c.ker = Nat.card K := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hkerc]
  obtain ⟨m, hm⟩ : ∃ m : P →* Q ⧸ N, ∀ p : P, m p = QuotientGroup.mk (p : Q) :=
    ⟨(QuotientGroup.mk' N).comp P.subtype, fun p => rfl⟩
  have hmker : m.ker.map P.subtype = N := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 : (QuotientGroup.mk (p : Q) : Q ⧸ N) = 1 := by
        rw [← hm p]
        exact hp
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro hx
      have hxP : x ∈ P := (hP x).mpr (N.mul_mem (N.inv_mem (hσN x hx)) hx)
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hm]
      exact (QuotientGroup.eq_one_iff x).mpr hx
  have hmker_card : Nat.card m.ker = 2 := by
    rw [← Subgroup.card_map_of_injective P.subtype_injective, hmker, hN2]
  have hsplit1 := card_eq_ker_mul_range m
  have hsplit2 := card_eq_ker_mul_range c
  have hprod : Nat.card c.ker * Nat.card c.range ≤ Nat.card c.ker * 2 :=
    Nat.mul_le_mul le_rfl hrange2
  have hRK : Nat.card m.range ≤ Nat.card K := by
    rw [hmker_card] at hsplit1
    omega
  have hmem : ∀ y : Q ⧸ N, QuotientGroup.congr N N σ hσ y = y → y ∈ m.range := by
    intro y hy
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : (σ q)⁻¹ * q ∈ N := by
      have h2 : (QuotientGroup.mk (σ q) : Q ⧸ N) = QuotientGroup.mk q := by
        rw [← QuotientGroup.congr_mk N N σ hσ q]
        exact hy
      exact QuotientGroup.eq.mp h2
    exact MonoidHom.mem_range.mpr ⟨⟨q, (hP q).mpr h1⟩, hm ⟨q, (hP q).mpr h1⟩⟩
  have hinj : Nat.card {y : Q ⧸ N // QuotientGroup.congr N N σ hσ y = y} ≤
      Nat.card m.range := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, hmem y.1 y.2⟩) ?_
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : m.range => z.1) hab
  have hfin : Nat.card K = Nat.card {q : Q // σ q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => hK x))
  exact le_trans hinj (by omega)

end Quotient

section Base

theorem four_card_ne_one {Q : Type} [Group Q] [Finite Q] (h4 : Nat.card Q = 4) :
    Nat.card {q : Q // q ≠ 1} = 3 := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl (fun q : Q => q = 1))
  rw [Nat.card_sum, h4] at h
  change Nat.card {q : Q // q = 1} + Nat.card {q : Q // q ≠ 1} = 4 at h
  have h1 : Nat.card {q : Q // q = 1} = 1 := by
    have := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_eq]
  omega

theorem four_false_of_card_four {Q F : Type} [Group Q] [Finite Q] [Group F] [Finite F]
    (hF : IsPGroup 2 F) (hF4 : 4 ≤ Nat.card F) (hQ4 : Nat.card Q = 4) (φ : F →* MulAut Q)
    (hfix : ∀ f : F, f ≠ 1 → Nat.card {q : Q // φ f q = q} ≤ 2) : False := by
  classical
  have hT : Nat.card {q : Q // q ≠ 1} = 3 := four_card_ne_one hQ4
  letI : MulAction F {q : Q // q ≠ 1} :=
    { smul := fun f t => ⟨φ f (t : Q), fun h => t.2 ((MulEquiv.map_eq_one_iff (φ f)).mp h)⟩
      one_smul := fun t => Subtype.ext (show φ 1 (t : Q) = t by simp)
      mul_smul := fun f g t => Subtype.ext (show φ (f * g) (t : Q) = φ f (φ g (t : Q)) by
        rw [map_mul, MulAut.mul_apply]) }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : F →* Equiv.Perm {q : Q // q ≠ 1},
      ∀ (f : F) (t : {q : Q // q ≠ 1}), ρ f t = f • t :=
    ⟨MulAction.toPermHom F _, fun f t => rfl⟩
  have hperm : Nat.card (Equiv.Perm {q : Q // q ≠ 1}) = 6 := by
    rw [Nat.card_perm, hT]
    rfl
  have hR : IsPGroup 2 ρ.range := hF.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hR
  have hdvd : Nat.card ρ.range ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    rwa [hperm] at h
  have hrange : Nat.card ρ.range ≤ 2 := by
    rw [hk] at hdvd ⊢
    have h6 : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hk3 : k < 3 := by
      by_contra hcon
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    · norm_num
    · norm_num
    · exact absurd hdvd (by norm_num)
  have hsplit := card_eq_ker_mul_range ρ
  have hker2 : 2 ≤ Nat.card ρ.ker := by
    by_contra hcon
    have h1 : Nat.card ρ.ker * Nat.card ρ.range ≤ 1 * 2 :=
      Nat.mul_le_mul (by omega) hrange
    omega
  have hnt : Nontrivial ρ.ker := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (1 : ρ.ker)
  have hf1 : f ≠ 1 := fun h => hne (Subtype.ext h)
  have hfρ : ρ f = 1 := MonoidHom.mem_ker.mp hf
  have hall : ∀ q : Q, φ f q = q := by
    intro q
    by_cases hq : q = 1
    · subst hq
      simp
    · have h1 : ρ f ⟨q, hq⟩ = ⟨q, hq⟩ := by
        rw [hfρ, Equiv.Perm.one_apply]
      have h2 : ((ρ f ⟨q, hq⟩ : {q : Q // q ≠ 1}) : Q) = q := by
        rw [h1]
      rw [hρ] at h2
      exact h2
  have hcardF : Nat.card {q : Q // φ f q = q} = 4 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun q => φ f q = q) hall), hQ4]
  have h3 := hfix f hf1
  omega

end Base

section Main

theorem four_card_le_two_aux {F : Type} [Group F] [Finite F] (hF : IsPGroup 2 F)
    (hF4 : 4 ≤ Nat.card F) (n : ℕ) :
    ∀ (Q : Type) [Group Q] [Finite Q], Nat.card Q = n → IsPGroup 2 Q →
      ∀ φ : F →* MulAut Q, (∀ f : F, f ≠ 1 → Nat.card {q : Q // φ f q = q} ≤ 2) →
        Nat.card Q ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q _ _ hn hQ φ hfix
    by_contra hlt
    have hlt2 : 2 < Nat.card Q := by omega
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
    have hQ4 : 4 ≤ Nat.card Q := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · norm_num at hk
          omega
        · norm_num at hk
          omega
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
          _ = Nat.card Q := hk.symm
    obtain ⟨w, hw1, hw2, hwc, hwφ⟩ := four_exists_central_involution hQ hF hQ4 φ
    have hNc : Subgroup.zpowers w ≤ Subgroup.center Q :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hwc)
    have hord : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2 : w ^ 2 = 1) hw1
    have hN2 : Nat.card (Subgroup.zpowers w) = 2 := by
      rw [Nat.card_zpowers, hord]
    have : (Subgroup.zpowers w).Normal := four_normal_of_le_center hNc
    have hstab : ∀ f : F, (Subgroup.zpowers w).map (φ f : Q →* Q) = Subgroup.zpowers w := by
      intro f
      rw [MonoidHom.map_zpowers]
      show Subgroup.zpowers (φ f w) = Subgroup.zpowers w
      rw [hwφ f]
    have hQN2 : Nat.card (Q ⧸ Subgroup.zpowers w) * 2 = Nat.card Q := by
      have h := Subgroup.card_mul_index (Subgroup.zpowers w)
      rw [hN2, Subgroup.index_eq_card] at h
      omega
    have hfix' : ∀ f : F, f ≠ 1 →
        Nat.card {y : Q ⧸ Subgroup.zpowers w //
          fourInducedHom φ (Subgroup.zpowers w) hstab f y = y} ≤ 2 := fun f hf =>
      (four_card_fixed_quotient_le (Subgroup.zpowers w) hN2 hNc (φ f) (hstab f)).trans
        (hfix f hf)
    have hle := ih (Nat.card (Q ⧸ Subgroup.zpowers w)) (by omega) (Q ⧸ Subgroup.zpowers w)
      rfl (hQ.to_quotient (Subgroup.zpowers w)) (fourInducedHom φ (Subgroup.zpowers w) hstab)
      hfix'
    exact four_false_of_card_four hF hF4 (by omega) φ hfix

end Main

theorem card_le_two_of_fourGroup {Q F : Type} [Group Q] [Finite Q] [Group F] [Finite F]
    (hQ : IsPGroup 2 Q) (hF : IsPGroup 2 F) (hF4 : 4 ≤ Nat.card F) (φ : F →* MulAut Q)
    (hfix : ∀ f : F, f ≠ 1 → Nat.card {q : Q // φ f q = q} ≤ 2) : Nat.card Q ≤ 2 :=
  four_card_le_two_aux hF hF4 (Nat.card Q) Q rfl hQ φ hfix

end CFSG.EvenSporadicStandard.Fin76b
