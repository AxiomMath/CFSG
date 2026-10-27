module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutC

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup GorensteinWalter AutL2Facts
open scoped commutatorElement

namespace AutD

theorem mem_zpowers_of_mem_inf {G : Type*} [Group G] [Finite G] {D A : Subgroup G} {δ g : G}
    (hδD : δ ∈ D) (hδA : δ ∈ A) (hδ : 2 * orderOf δ = Nat.card D)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hD : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a)
    (hg : g ∈ A ⊓ D) : g ∈ zpowers δ := by
  have hle : zpowers δ ≤ A ⊓ D := zpowers_le.mpr ⟨hδA, hδD⟩
  have hne : A ⊓ D ≠ D := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hD
    rw [← h] at ha hb
    exact hab (hA a ha.1 b hb.1)
  have h3 : Nat.card ↥(A ⊓ D) < Nat.card D := by
    by_contra h
    exact hne (eq_of_le_of_card_ge inf_le_right (not_lt.mp h))
  obtain ⟨k, hk⟩ := card_dvd_of_le hle
  rw [Nat.card_zpowers] at hk
  have hk2 : k < 2 := by
    rw [hk, ← hδ, mul_comm 2] at h3
    exact Nat.lt_of_mul_lt_mul_left h3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (Nat.card_pos (α := ↥(A ⊓ D))).ne' hk
  have hk1 : k = 1 := by omega
  rw [hk1, mul_one] at hk
  have h5 : zpowers δ = A ⊓ D := eq_of_le_of_card_ge hle (by rw [hk, Nat.card_zpowers])
  rw [h5]
  exact hg

theorem mulAut_conj_conj {Y : Type*} [Group Y] (α : MulAut Y) (s : Y) :
    α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := by
  ext g
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem commutator_mem {G : Type*} [Group G] {U : Subgroup G} {w a b : G} (hwU : w ∉ U)
    (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) (ha : a ∈ U ⊔ zpowers w)
    (hb : b ∈ U ⊔ zpowers w) : ⁅a, b⁆ ∈ U := by
  rw [commutatorElement_def]
  obtain ⟨u, hu, ha'⟩ :=
    (GorensteinWalter.mem_sup_zpowers_of_involution_inverts hwU hww hwinv).mp ha
  obtain ⟨v, hv, hb'⟩ :=
    (GorensteinWalter.mem_sup_zpowers_of_involution_inverts hwU hww hwinv).mp hb
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rw [ha', hb']
  · exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
  · have h1 : u * (v * w) * u⁻¹ * (v * w)⁻¹ = u * v * (w * u⁻¹ * w⁻¹) * v⁻¹ := by group
    rw [h1, hwinv _ (inv_mem hu)]
    exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem (inv_mem hu))) (inv_mem hv)
  · have h1 : u * w * v * (u * w)⁻¹ * v⁻¹ = u * (w * v * w⁻¹) * u⁻¹ * v⁻¹ := by group
    rw [h1, hwinv _ hv]
    exact mul_mem (mul_mem (mul_mem hu (inv_mem hv)) (inv_mem hu)) (inv_mem hv)
  · have h1 : u * w * (v * w) * (u * w)⁻¹ * (v * w)⁻¹ = u * (w * (v * u⁻¹) * w⁻¹) * v⁻¹ := by
      group
    rw [h1, hwinv _ (mul_mem hv (inv_mem hu))]
    exact mul_mem (mul_mem hu (inv_mem (mul_mem hv (inv_mem hu)))) (inv_mem hv)

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem right_eq_one_of_two_pow (hAut : Odd (Nat.card (F ≃+* F))) {X : PGammaL2 F} {k : ℕ}
    (hX : X ^ 2 ^ k = 1) : X.right = 1 := by
  have h1 : X.right ^ 2 ^ k = 1 := by
    have := congrArg (fieldProj F) hX
    rwa [map_pow, map_one] at this
  have h2 : orderOf X.right ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf X.right ∣ Nat.card (F ≃+* F) := _root_.orderOf_dvd_natCard _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  · exfalso
    rw [hi, pow_succ] at h3
    exact (Nat.not_even_iff_odd.mpr hAut) (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans h3))

theorem split_data (h2 : (2 : F) ≠ 0) :
    ∃ A₀ : Subgroup (PGammaL2 F), (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) ∧
      (∀ X ∈ centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F)),
        ∀ X' ∈ centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F)),
          ⁅X, X'⁆ ∈ A₀) ∧
      (∀ X ∈ centralizer ({SemidirectProduct.inl (tor F (-1))} : Set (PGammaL2 F)),
        X.right = 1 → X * X ≠ 1 → X ∈ A₀) := by
  refine ⟨((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (tor F)).range, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm a b]
  · intro X hX X' hX'
    obtain ⟨a, ε, ha⟩ :=
      (commute_tor_neg_one_iff h2 X).mp (mem_centralizer_singleton_iff.mp hX)
    obtain ⟨b, ε', hb⟩ :=
      (commute_tor_neg_one_iff h2 X').mp (mem_centralizer_singleton_iff.mp hX')
    obtain ⟨c, hc⟩ := commutator_nm a b ε ε' X.right X'.right
    have hστ : X.right * X'.right * X.right⁻¹ * X'.right⁻¹ = 1 := by
      rw [ringAut_comm X.right X'.right]
      group
    refine ⟨c, ?_⟩
    calc ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (tor F)) c =
        nm F c false (X.right * X'.right * X.right⁻¹ * X'.right⁻¹) := by
          rw [hστ, MonoidHom.comp_apply, inl_tor]
      _ = nm F a ε X.right * nm F b ε' X'.right * (nm F a ε X.right)⁻¹ *
          (nm F b ε' X'.right)⁻¹ := hc.symm
      _ = ⁅X, X'⁆ := by rw [commutatorElement_def, ← ha, ← hb]
  · intro X hX hr hXX
    obtain ⟨a, ε, ha⟩ :=
      (commute_tor_neg_one_iff h2 X).mp (mem_centralizer_singleton_iff.mp hX)
    rw [hr] at ha
    cases ε
    · exact ⟨a, by rw [MonoidHom.comp_apply, inl_tor, ha]⟩
    · exfalso
      apply hXX
      have htw : a * twist F true (fu F 1 a) = 1 := by
        show a * twist F true a = 1
        simp only [twist, mul_inv_cancel]
      rw [ha, nm_mul, htw, Bool.xor_self, mul_one, nm_one]

omit [Finite F] in
theorem nonsplit_data {U : Subgroup (PGL2 F)} {s w : PGL2 F}
    (hCs : centralizer ({s} : Set (PGL2 F)) = U ⊔ zpowers w) (hwU : w ∉ U) (hww : w * w = 1)
    (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) :
    ∃ A₀ : Subgroup (PGammaL2 F), (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) ∧
      (∀ X ∈ centralizer ({SemidirectProduct.inl s} : Set (PGammaL2 F)),
        ∀ X' ∈ centralizer ({SemidirectProduct.inl s} : Set (PGammaL2 F)),
          X.right = 1 → X'.right = 1 → ⁅X, X'⁆ ∈ A₀) ∧
      (∀ X ∈ centralizer ({SemidirectProduct.inl s} : Set (PGammaL2 F)),
        X.right = 1 → X * X ≠ 1 → X ∈ A₀) := by
  have hlin : ∀ X ∈ centralizer ({SemidirectProduct.inl s} : Set (PGammaL2 F)), X.right = 1 →
      X = SemidirectProduct.inl X.left ∧ X.left ∈ U ⊔ zpowers w := by
    intro X hX hr
    have hX' : X = SemidirectProduct.inl X.left := SemidirectProduct.ext rfl hr
    refine ⟨hX', ?_⟩
    rw [← hCs, mem_centralizer_singleton_iff]
    have h1 : (SemidirectProduct.inl (X.left * s) : PGammaL2 F) =
        SemidirectProduct.inl (s * X.left) := by
      rw [map_mul, map_mul, ← hX']
      exact mem_centralizer_singleton_iff.mp hX
    exact SemidirectProduct.inl_injective h1
  refine ⟨U.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hUc a ha b hb]
  · intro X hX X' hX' hr hr'
    obtain ⟨hXe, hXU⟩ := hlin X hX hr
    obtain ⟨hX'e, hX'U⟩ := hlin X' hX' hr'
    refine ⟨⁅X.left, X'.left⁆, commutator_mem hwU hww hwinv hXU hX'U, ?_⟩
    rw [map_commutatorElement, ← hXe, ← hX'e]
  · intro X hX hr hXX
    obtain ⟨hXe, hXU⟩ := hlin X hX hr
    refine ⟨X.left, AutC.mem_of_mem_sup_of_ne hwU hww hwinv hXU fun h => hXX ?_, hXe.symm⟩
    rw [hXe, ← map_mul, h, map_one]

end AutD

theorem autPSL2RDerived : AutPSL2RDerivedInput := by
  intro Y _ _ p n hp hp2 hY R ⟨Q, hQ⟩ hR8 δ hδR hδo P hP2 hRP
  subst hQ
  obtain ⟨-, hn1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hodd := isOddPrimePower_of hp hp2 hn1 hF
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ := autEquiv e with hΦ
  have hΦc : ∀ y : Y, Φ (MulAut.conj y) = incl F (e y) := fun y => autEquiv_conj e y
  have hconj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    intro a b hab
    apply e.injective
    apply incl_injective F
    rw [← hΦc, ← hΦc]
    exact congrArg Φ hab
  have hR' : ∀ t : Y, MulAut.conj t ∈ P → t ∈ (Q : Subgroup Y) := by
    intro t ht
    have h1 := Q.is_maximal' (hP2.comap_of_injective _ hconj) (fun r hr => hRP r hr)
    rw [← h1]
    exact ht
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, ∃ t ∈ (Q : Subgroup Y), ⁅x, y⁆ = MulAut.conj t := by
    intro x hx y hy
    obtain ⟨d, hd⟩ : ⁅Φ x, Φ y⁆ ∈ (incl F).range := commutator_mem_pslRange _ _
    have h1 : ⁅x, y⁆ = MulAut.conj (e.symm d) := by
      apply Φ.injective
      rw [hΦc, MulEquiv.apply_symm_apply, hd, map_commutatorElement]
    refine ⟨e.symm d, hR' _ ?_, h1⟩
    rw [← h1, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  obtain ⟨m, hm1, ⟨ρ⟩⟩ := sylow_two_dihedral_of_equiv e hodd Q
  have hQcard : Nat.card (Q : Subgroup Y) = 2 * 2 ^ m := by
    rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card]
  have hm4 : 4 ≤ 2 ^ m := by omega
  have hZcard : Nat.card (center ↥(Q : Subgroup Y)) = 2 := by
    rw [Nat.card_congr (centerCongr ρ).toEquiv]
    exact CFSG.Walter.card_center_dihedralGroup hm4 ((Nat.even_pow' (by omega)).mpr even_two)
  have hQnab : ∃ a ∈ (Q : Subgroup Y), ∃ b ∈ (Q : Subgroup Y), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : center ↥(Q : Subgroup Y) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact mem_center_iff.mpr fun r => Subtype.ext (h r r.2 g g.2)
    rw [htop, Subgroup.card_top, hQcard] at hZcard
    omega
  obtain ⟨z, hzQ, hzc, hz1, hzu, hzo⟩ : ∃ z ∈ (Q : Subgroup Y),
      (∀ r ∈ (Q : Subgroup Y), r * z = z * r) ∧ z ≠ 1 ∧
      (∀ y ∈ (Q : Subgroup Y), (∀ r ∈ (Q : Subgroup Y), r * y = y * r) → y ≠ 1 → y = z) ∧
      z ^ 2 = 1 := by
    obtain ⟨a₀, b₀, hab₀, huniv⟩ := Nat.card_eq_two_iff.mp hZcard
    obtain ⟨z', hz'1, hz'u⟩ : ∃ z : center ↥(Q : Subgroup Y), z ≠ 1 ∧
        ∀ w : center ↥(Q : Subgroup Y), w ≠ 1 → w = z := by
      have hmem : ∀ w : center ↥(Q : Subgroup Y), w = a₀ ∨ w = b₀ := fun w => by
        have : w ∈ ({a₀, b₀} : Set _) := by rw [huniv]; trivial
        simpa using this
      rcases hmem 1 with h1 | h1
      · refine ⟨b₀, fun h => hab₀ (h1.symm.trans h.symm), fun w hw => ?_⟩
        rcases hmem w with h | h
        · exact absurd (h.trans h1.symm) hw
        · exact h
      · refine ⟨a₀, fun h => hab₀ (h.trans h1), fun w hw => ?_⟩
        rcases hmem w with h | h
        · exact h
        · exact absurd (h.trans h1.symm) hw
    have hval : ∀ w w' : center ↥(Q : Subgroup Y),
        ((w : ↥(Q : Subgroup Y)) : Y) = ((w' : ↥(Q : Subgroup Y)) : Y) → w = w' :=
      fun w w' h => Subtype.ext (Subtype.ext h)
    refine ⟨((z' : ↥(Q : Subgroup Y)) : Y), (z' : ↥(Q : Subgroup Y)).2, fun r hr =>
      congrArg Subtype.val (mem_center_iff.mp z'.2 ⟨r, hr⟩), fun h => hz'1 (hval _ 1 h),
      fun y hy hyc hy1 => ?_, ?_⟩
    · have hyZ : (⟨y, hy⟩ : ↥(Q : Subgroup Y)) ∈ center ↥(Q : Subgroup Y) :=
        mem_center_iff.mpr fun r => Subtype.ext (hyc r r.2)
      have h1 := hz'u ⟨⟨y, hy⟩, hyZ⟩ fun h => hy1 (congrArg (fun w :
        center ↥(Q : Subgroup Y) => ((w : ↥(Q : Subgroup Y)) : Y)) h)
      exact congrArg (fun w : center ↥(Q : Subgroup Y) => ((w : ↥(Q : Subgroup Y)) : Y)) h1
    · have h1 : z' ^ Nat.card (center ↥(Q : Subgroup Y)) = 1 := pow_card_eq_one'
      rw [hZcard] at h1
      have := congrArg (fun w : center ↥(Q : Subgroup Y) => ((w : ↥(Q : Subgroup Y)) : Y)) h1
      simpa using this
  have hPQ : ∀ x ∈ P, ∀ r ∈ (Q : Subgroup Y), x r ∈ (Q : Subgroup Y) := by
    intro x hx r hr
    apply hR'
    rw [← AutD.mulAut_conj_conj]
    exact mul_mem (mul_mem hx (hRP r hr)) (inv_mem hx)
  have hPz : ∀ x ∈ P, x z = z := by
    intro x hx
    refine hzu (x z) (hPQ x hx z hzQ) (fun r hr => ?_)
      fun h => hz1 (x.injective (h.trans (map_one x).symm))
    have h1 := hzc _ (hPQ x⁻¹ (inv_mem hx) r hr)
    calc r * x z = x (x⁻¹ r) * x z := by rw [MulAut.apply_inv_self]
      _ = x (x⁻¹ r * z) := (map_mul x _ _).symm
      _ = x (z * x⁻¹ r) := by rw [h1]
      _ = x z * r := by rw [map_mul, MulAut.apply_inv_self]
  obtain ⟨z₀, hz₀, A₀, hA₀c, hA₀comm, hA₀lin⟩ : ∃ z₀ : PSL2 F,
      BenderSuzuki.PFAppendixIII.IsInvolution z₀ ∧ ∃ A₀ : Subgroup (PGammaL2 F),
        (∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) ∧
        (∀ X ∈ centralizer ({incl F z₀} : Set (PGammaL2 F)),
          ∀ X' ∈ centralizer ({incl F z₀} : Set (PGammaL2 F)),
            (∃ k : ℕ, X ^ 2 ^ k = 1) → (∃ k : ℕ, X' ^ 2 ^ k = 1) → ⁅X, X'⁆ ∈ A₀) ∧
        (∀ X ∈ centralizer ({incl F z₀} : Set (PGammaL2 F)), X.right = 1 → X * X ≠ 1 →
          X ∈ A₀) := by
    by_cases hsq : IsSquare (-1 : F)
    · obtain ⟨z₀, hz₀⟩ := exists_psl2_tor_neg_one hsq
      obtain ⟨A₀, h1, h2', h3⟩ := AutD.split_data h2
      refine ⟨z₀, ⟨fun h => tor_neg_one_ne_one h2 ?_, ?_⟩, A₀, h1,
        fun X hX X' hX' _ _ => h2' X (by rwa [← hz₀]) X' (by rwa [← hz₀]),
        fun X hX => h3 X (by rwa [← hz₀])⟩
      · have : incl F z₀ = 1 := by rw [h, map_one]
        rw [hz₀] at this
        exact SemidirectProduct.inl_injective (this.trans (map_one _).symm)
      · apply incl_injective F
        rw [map_pow, hz₀, ← map_pow, ← map_pow, neg_one_sq, map_one, map_one, map_one]
    · obtain ⟨hAut, U, s, w, -, -, s₀, hCs, hwU, hww, hwinv, hUc, -, -, -, -, -, hs₀, hs₀i⟩ :=
        AutC.exists_nonsplit_data hp hp2 hF hsq
      obtain ⟨A₀, h1, h2', h3⟩ := AutD.nonsplit_data hCs hwU hww hwinv hUc
      have hincl : incl F s₀ = SemidirectProduct.inl s := by rw [incl_apply, hs₀]
      refine ⟨s₀, hs₀i, A₀, h1, fun X hX X' hX' ⟨k, hk⟩ ⟨k', hk'⟩ => ?_,
        fun X hX => h3 X (by rwa [← hincl])⟩
      exact h2' X (by rwa [← hincl]) X' (by rwa [← hincl])
        (AutD.right_eq_one_of_two_pow hAut hk) (AutD.right_eq_one_of_two_pow hAut hk')
  have hez : BenderSuzuki.PFAppendixIII.IsInvolution (e z) := by
    refine ⟨fun h => hz1 (e.injective (h.trans (map_one e).symm)), ?_⟩
    rw [← map_pow, hzo, map_one]
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (e z) z₀ hez hz₀
  let ψ : MulAut Y →* PGammaL2 F := (MulAut.conj (incl F g)).toMonoidHom.comp Φ.toMonoidHom
  have hψ : ∀ a, ψ a = incl F g * Φ a * (incl F g)⁻¹ := fun a => rfl
  have hψinj : Function.Injective ψ := fun a b h => Φ.injective ((MulAut.conj _).injective h)
  have hψC : ∀ a : MulAut Y, a z = z → ψ a ∈ centralizer ({incl F z₀} : Set (PGammaL2 F)) := by
    intro a ha
    have h1 : a * MulAut.conj z = MulAut.conj z * a := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, ha]
    have h2 : Φ a * incl F (e z) = incl F (e z) * Φ a := by
      rw [← hΦc, ← map_mul, ← map_mul, h1]
    have h3 : incl F z₀ = incl F g * incl F (e z) * (incl F g)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hg]
    rw [mem_centralizer_singleton_iff, h3, hψ]
    calc incl F g * Φ a * (incl F g)⁻¹ * (incl F g * incl F (e z) * (incl F g)⁻¹) =
        incl F g * (Φ a * incl F (e z)) * (incl F g)⁻¹ := by group
      _ = incl F g * (incl F (e z) * Φ a) * (incl F g)⁻¹ := by rw [h2]
      _ = incl F g * incl F (e z) * (incl F g)⁻¹ * (incl F g * Φ a * (incl F g)⁻¹) := by group
  have hAc : ∀ a ∈ A₀.comap ψ, ∀ b ∈ A₀.comap ψ, a * b = b * a := by
    intro a ha b hb
    apply hψinj
    rw [map_mul, map_mul]
    exact hA₀c _ ha _ hb
  have hPk : ∀ a ∈ P, ∃ k : ℕ, ψ a ^ 2 ^ k = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := hP2 ⟨a, ha⟩
    refine ⟨k, ?_⟩
    have h1 : a ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, h1, map_one]
  have hPA : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ A₀.comap ψ := by
    intro x hx y hy
    show ψ ⁅x, y⁆ ∈ A₀
    rw [map_commutatorElement]
    exact hA₀comm _ (hψC x (hPz x hx)) _ (hψC y (hPz y hy)) (hPk x hx) (hPk y hy)
  have hδ4 : δ * δ ≠ 1 := by
    intro h
    have h1 : orderOf δ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    have h3 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hδA : MulAut.conj δ ∈ A₀.comap ψ := by
    show ψ (MulAut.conj δ) ∈ A₀
    refine hA₀lin _ (hψC _ ?_) ?_ ?_
    · rw [MulAut.conj_apply, hzc δ hδR, mul_inv_cancel_right]
    · rw [hψ, hΦc]
      simp [incl_apply]
    · intro h
      apply hδ4
      apply hconj
      apply hψinj
      rw [map_mul, map_mul, h, map_one, map_one]
  rw [MonoidHom.map_zpowers, commutator_le]
  intro x hx y hy
  obtain ⟨t, htQ, ht⟩ := hcomm x hx y hy
  refine AutD.mem_zpowers_of_mem_inf (D := (Q : Subgroup Y).map MulAut.conj) (A := A₀.comap ψ)
    (mem_map_of_mem _ hδR) hδA ?_ hAc ?_ ⟨hPA x hx y hy, ?_⟩
  · rw [orderOf_injective _ hconj, hδo]
    exact Nat.card_congr ((Q : Subgroup Y).equivMapOfInjective _ hconj).toEquiv
  · obtain ⟨a, ha, b, hb, hab⟩ := hQnab
    refine ⟨_, mem_map_of_mem _ ha, _, mem_map_of_mem _ hb, fun h => hab (hconj ?_)⟩
    rw [map_mul, map_mul]
    exact h
  · rw [ht]
    exact mem_map_of_mem _ htQ

end CFSG.ComponentClassification.HarrisLit
