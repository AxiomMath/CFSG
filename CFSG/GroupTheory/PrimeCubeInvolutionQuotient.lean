module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.GroupTheory

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_surjective_invariant_hom_of_nonabelian_card_pow_three
    (hp2 : p ≠ 2) {P : Type*} [Group P] [Finite P]
    (hPcard : Nat.card P = p ^ 3)
    (hPnc : ∃ x y : P, x * y ≠ y * x)
    (α : MulAut P) (hα : Function.Involutive α)
    (hαZ : ∀ z ∈ Subgroup.center P, α z = z⁻¹) :
    ∃ χ : P →* Multiplicative (ZMod p),
      Function.Surjective χ ∧ ∀ x, χ (α x) = χ x := by
  classical
  obtain ⟨-, hcardZ, hQcomm, hQpow, hQcard, -, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure
      (p := p) (S := P) hPcard hPnc
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := p) (W := P ⧸ Subgroup.center P) hQcomm hQpow (n := 2) hQcard
  have hfix : ∃ x : P, x ≠ 1 ∧ α x = x := by
    by_contra h
    have hfree : MonoidHom.FixedPointFree α.toMonoidHom := by
      intro x hx
      by_contra hx1
      exact h ⟨x, hx1, hx⟩
    obtain ⟨a, b, hab⟩ := hPnc
    exact hab (hfree.commute_all_of_involutive hα a b).eq
  obtain ⟨x, hx1, hxα⟩ := hfix
  have hxZ : x ∉ Subgroup.center P := by
    intro hxZ
    have hxinv : x⁻¹ = x := by
      calc x⁻¹ = α x := (hαZ x hxZ).symm
        _ = x := hxα
    have hx2 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = x⁻¹ * x := by rw [hxinv]
        _ = 1 := inv_mul_cancel x
    have hxp : x ^ p = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center P) (x := ⟨x, hxZ⟩)
      have h' : ((⟨x, hxZ⟩ : Subgroup.center P) ^ Nat.card (Subgroup.center P) : P) = 1 :=
        congrArg Subtype.val h
      simpa [hcardZ] using h'
    have hcop : Nat.Coprime 2 p :=
      Nat.coprime_two_left.mpr (hp.out.odd_of_ne_two hp2)
    have horder : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_iff_pow_eq_one.mpr hx2)
        (orderOf_dvd_iff_pow_eq_one.mpr hxp)
    exact hx1 (orderOf_eq_one_iff.mp horder)
  have hqx : (QuotientGroup.mk' (Subgroup.center P)) x ≠ 1 :=
    fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h)
  let u : Fin 2 → ZMod p :=
    Multiplicative.toAdd (e (QuotientGroup.mk' (Subgroup.center P) x))
  have hu : u ≠ 0 := by
    intro h
    apply hqx
    apply e.injective
    have h' : e (QuotientGroup.mk' (Subgroup.center P) x) = 1 := by
      simpa [u] using congrArg Multiplicative.ofAdd h
    simpa using h'
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hu
  let χ₀ : P →* Multiplicative (ZMod p) :=
    (AddMonoidHom.toMultiplicative ℓ.toAddMonoidHom).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center P)))
  have hχ₀x : χ₀ x = Multiplicative.ofAdd (1 : ZMod p) := by
    change Multiplicative.ofAdd (ℓ u) = Multiplicative.ofAdd (1 : ZMod p)
    rw [hℓ]
  let χ : P →* Multiplicative (ZMod p) := χ₀ * χ₀.comp α.toMonoidHom
  have hχinv : ∀ y, χ (α y) = χ y := by
    intro y
    simp [χ, hα y, mul_comm]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have hp3 : 3 ≤ p := hp.out.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  have hχx : χ x = Multiplicative.ofAdd (2 : ZMod p) := by
    calc χ x = χ₀ x * χ₀ (α x) := rfl
      _ = Multiplicative.ofAdd (1 : ZMod p) * Multiplicative.ofAdd (1 : ZMod p) := by
        rw [hxα, hχ₀x]
      _ = Multiplicative.ofAdd ((1 : ZMod p) + 1) := (ofAdd_add 1 1).symm
      _ = Multiplicative.ofAdd (2 : ZMod p) := by
        congr 1
        norm_num
  have hχx_ne : χ x ≠ 1 := by
    rw [hχx]
    simpa using h2ne
  have hfact : Fact (Nat.card (Multiplicative (ZMod p))).Prime :=
    ⟨by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]; exact hp.out⟩
  have hχrange : χ.range = ⊤ := by
    rcases @Subgroup.eq_bot_or_eq_top_of_prime_card
      (Multiplicative (ZMod p)) _ χ.range hfact with hbot | htop
    · have hxrange : χ x ∈ χ.range := ⟨x, rfl⟩
      exfalso
      exact hχx_ne (by simpa [hbot] using hxrange)
    · exact htop
  exact ⟨χ, MonoidHom.range_eq_top.mp hχrange, hχinv⟩

theorem exists_surjective_hom_of_nonabelian_card_pow_three_index_two
    (hp2 : p ≠ 2) {A : Type*} [Group A] [Finite A]
    (P : Subgroup A) [P.Normal]
    (hPcard : Nat.card P = p ^ 3)
    (hPnc : ∃ x y : P, x * y ≠ y * x)
    (hindex : P.index = 2)
    (t : A) (ht : orderOf t = 2)
    (hZ : ∀ z : Subgroup.center P,
      t * ((z : P) : A) * t⁻¹ = (((z : P) : A))⁻¹) :
    ∃ Ψ : A →* Multiplicative (ZMod p),
      Function.Surjective Ψ ∧
      Function.Surjective (Ψ.comp P.subtype) ∧ Ψ t = 1 := by
  classical
  let α : MulAut P := MulAut.conjNormal (H := P) t
  have ht2 : t * t = 1 := by
    simpa [pow_two, ht] using pow_orderOf_eq_one t
  have hα2 : α * α = 1 := by
    change MulAut.conjNormal (H := P) t * MulAut.conjNormal (H := P) t = 1
    rw [← map_mul, ht2, map_one]
  have hα : Function.Involutive α := by
    intro x
    have h := congrArg (fun β : MulAut P => β x) hα2
    simpa using h
  have hαZ : ∀ z ∈ Subgroup.center P, α z = z⁻¹ := by
    intro z hz
    apply Subtype.ext
    simpa [α, MulAut.conjNormal_apply] using hZ ⟨z, hz⟩
  obtain ⟨χ, hχsurj, hχinv⟩ :=
    exists_surjective_invariant_hom_of_nonabelian_card_pow_three
      (p := p) hp2 hPcard hPnc α hα hαZ
  let K : Subgroup A := Subgroup.zpowers t
  have hKcard : Nat.card K = 2 := by
    change Nat.card (Subgroup.zpowers t) = 2
    rw [Nat.card_zpowers, ht]
  have hcardPK : Nat.card P * Nat.card K = Nat.card A := by
    rw [hKcard, ← hindex]
    exact Subgroup.card_mul_index P
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hcop : Nat.Coprime (Nat.card P) (Nat.card K) := by
    rw [hPcard, hKcard]
    exact (Nat.coprime_pow_left_iff (n := 3) (by norm_num) p 2).mpr
      (Nat.coprime_two_right.mpr hpodd)
  have hPK : P.IsComplement' K := Subgroup.isComplement'_of_coprime hcardPK hcop
  let φ : K →* MulAut P :=
    (P.normalizerMonoidHom).comp (Subgroup.inclusion (P.normalizer_eq_top ▸ le_top))
  let e : P ⋊[φ] K ≃* A := SemidirectProduct.mulEquivSubgroup hPK
  have hφ_coe : ∀ (k : K) (y : P), ((φ k) y : A) = (k : A) * (y : A) * (k : A)⁻¹ := by
    intro k y
    dsimp only [φ]
    rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion]
  have hφapply : ∀ k : K, φ k = MulAut.conjNormal (H := P) (k : A) := by
    intro k
    ext y
    rw [hφ_coe k y, MulAut.conjNormal_apply]
  let Fixχ : Subgroup (MulAut P) :=
    { carrier := {β | ∀ y : P, χ (β y) = χ y}
      mul_mem' := fun {β γ} hβ hγ y => by
        rw [MulAut.mul_apply, hβ, hγ]
      one_mem' := fun y => by
        simp
      inv_mem' := fun {β} hβ y => by
        simpa using (hβ (β⁻¹ y)).symm }
  let FixA : Subgroup A := Fixχ.comap (MulAut.conjNormal (H := P))
  have htFixA : t ∈ FixA := by
    simpa [FixA, Fixχ, α] using hχinv
  have hKFixA : K ≤ FixA := Subgroup.zpowers_le.mpr htFixA
  have hcompat : ∀ k : K,
      χ.comp ((φ k).toMonoidHom) =
        (MulAut.conj ((1 : K →* Multiplicative (ZMod p)) k)).toMonoidHom.comp χ := by
    intro k
    ext y
    have hk : MulAut.conjNormal (H := P) (k : A) ∈ Fixχ := by
      simpa [FixA] using hKFixA k.2
    simpa [MonoidHom.comp_apply, hφapply k, MulAut.conjNormal_apply] using hk y
  let Ψ : A →* Multiplicative (ZMod p) :=
    (SemidirectProduct.lift (φ := φ) χ
      (1 : K →* Multiplicative (ZMod p)) hcompat).comp e.symm.toMonoidHom
  have hΨP : ∀ y : P, Ψ (y : A) = χ y := by
    intro y
    have h1 : e.symm (y : A) = SemidirectProduct.inl y := by
      rw [MulEquiv.symm_apply_eq]
      change (y : A) = SemidirectProduct.mulEquivSubgroup hPK (SemidirectProduct.inl y)
      rw [SemidirectProduct.mulEquivSubgroup_apply]
      simp
    simp [Ψ, h1]
  have hΨt : Ψ t = 1 := by
    let kt : K := ⟨t, Subgroup.mem_zpowers t⟩
    have h1 : e.symm t = SemidirectProduct.inr kt := by
      rw [MulEquiv.symm_apply_eq]
      change t = SemidirectProduct.mulEquivSubgroup hPK (SemidirectProduct.inr kt)
      rw [SemidirectProduct.mulEquivSubgroup_apply]
      simp [kt]
    simp [Ψ, h1]
  refine ⟨Ψ, ?_, ?_, hΨt⟩
  · intro z
    obtain ⟨y, hy⟩ := hχsurj z
    exact ⟨(y : A), by rw [hΨP y, hy]⟩
  · intro z
    obtain ⟨y, hy⟩ := hχsurj z
    exact ⟨y, by simpa [hΨP y] using hy⟩

theorem exists_normal_index_p_containing_of_nonabelian_card_pow_three_index_two
    (hp2 : p ≠ 2) {A : Type*} [Group A] [Finite A]
    (P : Subgroup A) [P.Normal]
    (hPcard : Nat.card P = p ^ 3)
    (hPnc : ∃ x y : P, x * y ≠ y * x)
    (hindex : P.index = 2)
    (t : A) (ht : orderOf t = 2)
    (hZ : ∀ z : Subgroup.center P,
      t * ((z : P) : A) * t⁻¹ = (((z : P) : A))⁻¹) :
    ∃ N : Subgroup A, N.Normal ∧ N.index = p ∧ t ∈ N := by
  obtain ⟨Ψ, hΨsurj, -, hΨt⟩ :=
    exists_surjective_hom_of_nonabelian_card_pow_three_index_two
      (p := p) hp2 P hPcard hPnc hindex t ht hZ
  refine ⟨Ψ.ker, MonoidHom.normal_ker Ψ, ?_, ?_⟩
  · rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hΨsurj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · exact MonoidHom.mem_ker.mpr hΨt

theorem exists_normal_index_three_containing_of_nonabelian_card_twenty_seven_index_two
    {A : Type*} [Group A] [Finite A]
    (P : Subgroup A) [P.Normal]
    (hPcard : Nat.card P = 27)
    (hPnc : ∃ x y : P, x * y ≠ y * x)
    (hindex : P.index = 2)
    (t : A) (ht : orderOf t = 2)
    (hZ : ∀ z : Subgroup.center P,
      t * ((z : P) : A) * t⁻¹ = (((z : P) : A))⁻¹) :
    ∃ N : Subgroup A, N.Normal ∧ N.index = 3 ∧ t ∈ N :=
  exists_normal_index_p_containing_of_nonabelian_card_pow_three_index_two
    (p := 3) (by norm_num) P (by simpa using hPcard) hPnc hindex t ht hZ

end CFSG.GroupTheory
