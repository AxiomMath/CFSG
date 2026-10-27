module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129Q
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129g

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129j

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129d
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)

section Impl

variable {Y : Type} [Group Y]

theorem exists_perm_implementer {K₀ : Subgroup Y} {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (ψ : K₀ ≃* alternatingGroup (Fin n)) {H : Subgroup Y}
    (hH : H ≤ Subgroup.normalizer (K₀ : Set Y)) :
    ∃ ρ : ↥H →* Equiv.Perm (Fin n), ∀ (h : ↥H) (x y : ↥K₀),
      (y : Y) = (h : Y) * (x : Y) * (h : Y)⁻¹ →
        ((ψ y : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
          ρ h * ((ψ x : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * (ρ h)⁻¹ := by
  have bij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let e : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ bij
  let act : ↥H →* MulAut K₀ := K₀.normalizerMonoidHom.comp (Subgroup.inclusion hH)
  let ρ : ↥H →* Equiv.Perm (Fin n) :=
    e.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp act)
  have hρ : ∀ h : ↥H, e (ρ h) = MulAut.congr ψ (act h) := fun h => e.apply_symm_apply _
  refine ⟨ρ, fun h x y hy => ?_⟩
  have hact : act h x = y := by
    apply Subtype.ext
    have : ((act h x : K₀) : Y) = (h : Y) * (x : Y) * (h : Y)⁻¹ := by
      show ((K₀.normalizerMonoidHom ⟨(h : Y), hH h.2⟩ x : K₀) : Y) = _
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [this, hy]
  have h1 : ψ y = e (ρ h) (ψ x) := by
    rw [hρ h, ← hact]
    simp [MulAut.congr_apply]
  rw [h1]
  show ((MulAut.conjNormal (ρ h) (ψ x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = _
  rw [MulAut.conjNormal_apply]

end Impl

section Perm

variable {G : Type} [Group G] [Finite G] {N K F : Subgroup G}

theorem perm_comm_of_fix_of_supp {Ω₀ : Set (Fin 13)} {a b : Equiv.Perm (Fin 13)}
    (ha : ∀ j ∈ Ω₀, a j = j) (hb : ∀ j, j ∉ Ω₀ → b j = j) : a * b = b * a := by
  refine Equiv.ext fun p => ?_
  by_cases hp : p ∈ Ω₀
  · have hbp : b p ∈ Ω₀ := by
      by_contra h
      have hbpp : b p = p := b.injective (hb _ h)
      apply h
      rw [hbpp]
      exact hp
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha _ hp, ha _ hbp]
  · have hap : a p ∉ Ω₀ := by
      intro h
      have happ : a p = p := a.injective (ha _ h)
      exact hp (happ ▸ h)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hb _ hp, hb _ hap]

theorem exists_x_zeta {n : ℕ} (hn13 : n = 13)
    (ψ : ↥(barX 3 N K) ≃* alternatingGroup (Fin n)) (Ω₀ : Set (Fin n)) (hΩ₀ : Ω₀.ncard = 4)
    (hFK : barX 3 N F ≤ barX 3 N K) (hFel : IsElemAbelian 3 (barX 3 N F))
    (hFcard : Nat.card (barX 3 N F) = 9)
    (hFfix : ∀ g ∈ permImage ψ (barX 3 N F), ∀ j ∈ Ω₀, g j = j)
    (htrans : ∀ j k : Fin n, j ∉ Ω₀ → k ∉ Ω₀ →
      ∃! g : Equiv.Perm (Fin n), g ∈ permImage ψ (barX 3 N F) ∧ g j = k)
    {y : ↥N ⧸ GLAPPrimeCore 3 ↥N} (hyF : y ∈ barX 3 N F) (hy1 : y ≠ 1)
    {c₀ : ↥N ⧸ GLAPPrimeCore 3 ↥N} (hc₀K : c₀ ∈ barX 3 N K)
    {σ : Equiv.Perm (Fin n)} (hσ : σ.IsThreeCycle) (hσsupp : ∀ j, j ∉ Ω₀ → σ j = j)
    (hperm : permImage ψ (Subgroup.zpowers c₀) = Subgroup.zpowers σ) :
    ∃ x ∈ barX 3 N K, orderOf x = 3 ∧
      (∀ f ∈ barX 3 N F, ∀ j : ℕ,
        x * (f * c₀ ^ j) * x⁻¹ * (f * c₀ ^ j)⁻¹ ∈ Subgroup.zpowers y) ∧
      ∀ S₀ : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N),
        S₀ ≤ Subgroup.normalizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) →
        IsPGroup 2 ↥S₀ → (∀ s ∈ S₀, ∀ f ∈ barX 3 N F, s * f = f * s) →
        (∀ s ∈ S₀, s * x = x * s) ∧
        ((¬ S₀ ≤ Subgroup.centralizer (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))) →
          ∃ s ∈ S₀, ∃ ζ ∈ barX 3 N K, ζ * x = x * ζ ∧ orderOf (ζ * s * ζ⁻¹ * s⁻¹) = 3) := by
  subst hn13
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyK : y ∈ barX 3 N K := hFK hyF
  let yK : ↥(barX 3 N K) := ⟨y, hyK⟩
  let cK : ↥(barX 3 N K) := ⟨c₀, hc₀K⟩
  have hF'el : IsElemAbelian 3 (permImage ψ (barX 3 N F)) := permImage_elemAbelian ψ hFel
  have hF'card : Nat.card (permImage ψ (barX 3 N F)) = 9 := by
    rw [permImage_card ψ hFK, hFcard]
  have hy'F : ((ψ yK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) ∈
      permImage ψ (barX 3 N F) := (mem_permImage ψ).2 ⟨yK, hyF, rfl⟩
  have hy'1 : ((ψ yK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) ≠ 1 := by
    intro h1
    apply hy1
    have h2 : ψ yK = 1 := Subtype.ext h1
    have h3 : yK = 1 := ψ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  obtain ⟨x', hx'alt, hx'1, hx'3, hx'fix, hx'comm, c, c', hc, hc', hcc', hxc, hxc'⟩ :=
    Lemma129Q.permB Ω₀ hΩ₀ _ hF'el hF'card hFfix htrans hy'F hy'1 hσ hσsupp
  let xK : ↥(barX 3 N K) := ψ.symm ⟨x', hx'alt⟩
  have hψx : ((ψ xK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) = x' := by
    simp [xK]
  have hxord : orderOf xK = 3 := by
    rw [← MulEquiv.orderOf_eq ψ xK, ← Subgroup.orderOf_coe (ψ xK), hψx]
    exact orderOf_eq_prime hx'3 hx'1
  refine ⟨(xK : ↥N ⧸ GLAPPrimeCore 3 ↥N), xK.2, by rw [Subgroup.orderOf_coe]; exact hxord,
    ?_, ?_⟩
  · intro f hf j
    have hfK : f ∈ barX 3 N K := hFK hf
    let fK : ↥(barX 3 N K) := ⟨f, hfK⟩
    let gK : ↥(barX 3 N K) := fK * cK ^ j
    have hψg : ((ψ gK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) ∈
        permImage ψ (barX 3 N F) ⊔ Subgroup.zpowers σ := by
      have h1 : ((ψ gK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) =
          ((ψ fK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) *
            ((ψ cK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) ^ j := by
        simp [gK]
      rw [h1]
      refine Subgroup.mul_mem_sup ((mem_permImage ψ).2 ⟨fK, hf, rfl⟩) (Subgroup.pow_mem _ ?_ j)
      rw [← hperm]
      exact (mem_permImage ψ).2 ⟨cK, Subgroup.mem_zpowers c₀, rfl⟩
    have hcomm := hx'comm _ hψg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcomm
    have hu : xK * gK * xK⁻¹ * gK⁻¹ = yK ^ k := by
      apply ψ.injective
      apply Subtype.ext
      simp only [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, hψx, map_zpow,
        SubgroupClass.coe_zpow]
      exact hk.symm
    have h2 := congrArg Subtype.val hu
    refine ⟨k, ?_⟩
    simpa [gK] using h2.symm
  · intro S₀ hS₀ hS₂ hSF
    obtain ⟨ρ, hρ⟩ := exists_perm_implementer (K₀ := barX 3 N K) (n := 13) (by norm_num)
      (by norm_num) ψ hS₀
    have hρfix : ∀ s : ↥S₀, ∀ j, j ∉ Ω₀ → (ρ s) j = j := by
      intro s
      refine Lemma129Q.permC Ω₀ (permImage ψ (barX 3 N F)) hF'el hF'card hFfix htrans ?_ ?_
      · obtain ⟨k, hk⟩ := hS₂ s
        exact ⟨k, by rw [← map_pow, hk, map_one]⟩
      · intro g hg
        obtain ⟨fK, hfK, rfl⟩ := (mem_permImage ψ).1 hg
        have h1 := hρ s fK fK (by
          have := hSF s s.2 fK hfK
          calc (fK : ↥N ⧸ GLAPPrimeCore 3 ↥N) = (fK : ↥N ⧸ GLAPPrimeCore 3 ↥N) * s * (s : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ := by group
            _ = (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * fK * (s : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ := by rw [this]
            )
        calc ρ s * ((ψ fK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13))
            = (ρ s * ((ψ fK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) * (ρ s)⁻¹) * ρ s := by group
          _ = ((ψ fK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) * ρ s := by rw [← h1]
    have hxcomm : ∀ s : ↥S₀, (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) =
        (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) := by
      intro s
      have hmem : (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
          (s : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ ∈ barX 3 N K :=
        (Subgroup.mem_normalizer_iff.1 (hS₀ s.2) _).1 xK.2
      have h1 := hρ s xK ⟨_, hmem⟩ rfl
      have h2 : ρ s * x' = x' * ρ s := (perm_comm_of_fix_of_supp hx'fix (hρfix s)).symm
      have h3 : ((ψ ⟨_, hmem⟩ : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) = x' := by
        rw [h1, hψx, h2]
        group
      have h4 : (⟨_, hmem⟩ : ↥(barX 3 N K)) = xK :=
        ψ.injective (Subtype.ext (h3.trans hψx.symm))
      have h5 : (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
          (s : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ = (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) :=
        congrArg Subtype.val h4
      calc (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N)
          = ((s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) *
              (s : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹) * s := by group
        _ = (xK : ↥N ⧸ GLAPPrimeCore 3 ↥N) * s := by rw [h5]
    refine ⟨fun s hs => hxcomm ⟨s, hs⟩, fun hnc => ?_⟩
    obtain ⟨s, hsS, hsK⟩ : ∃ s ∈ S₀, s ∉ Subgroup.centralizer
        (barX 3 N K : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := by
      by_contra hcon
      push Not at hcon
      exact hnc fun s hs => hcon s hs
    let s' : ↥S₀ := ⟨s, hsS⟩
    have hρ1 : ρ s' ≠ 1 := by
      intro h1
      apply hsK
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hmem : s * k * s⁻¹ ∈ barX 3 N K := (Subgroup.mem_normalizer_iff.1 (hS₀ hsS) _).1 hk
      have h2 := hρ s' ⟨k, hk⟩ ⟨_, hmem⟩ rfl
      rw [h1] at h2
      simp only [map_one, one_mul, inv_one, mul_one] at h2
      have h3 : (⟨_, hmem⟩ : ↥(barX 3 N K)) = ⟨k, hk⟩ := ψ.injective (Subtype.ext h2)
      have h4 : s * k * s⁻¹ = k := congrArg Subtype.val h3
      calc k * s = (s * k * s⁻¹) * s := by rw [h4]
        _ = s * k := by group
    obtain ⟨ω, hω⟩ : ∃ ω, ρ s' ω ≠ ω := by
      by_contra hcon
      push Not at hcon
      exact hρ1 (Equiv.ext hcon)
    have hωΩ : ω ∈ Ω₀ := by
      by_contra hn
      exact hω (hρfix s' ω hn)
    obtain ⟨ζ, hζ3, hζsupp, hζcomm⟩ := Lemma129Q.permD (hρfix s') hωΩ hω hc hc' hcc'
    have hζalt : ζ ∈ alternatingGroup (Fin 13) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hζ3.sign
    let ζK : ↥(barX 3 N K) := ψ.symm ⟨ζ, hζalt⟩
    have hψζ : ((ψ ζK : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) = ζ := by
      simp [ζK]
    refine ⟨s, hsS, (ζK : ↥N ⧸ GLAPPrimeCore 3 ↥N), ζK.2, ?_, ?_⟩
    · have hdisj : ζ * x' = x' * ζ := by
        have hD : Equiv.Perm.Disjoint ζ x' := by
          intro j
          by_cases hj : ζ j = j
          · exact Or.inl hj
          · right
            rcases hζsupp j hj with rfl | rfl | rfl
            · exact hx'fix _ hωΩ
            · exact hxc
            · exact hxc'
        exact hD.commute.eq
      have h1 : ζK * xK = xK * ζK := by
        apply ψ.injective
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul, hψζ, hψx]
        exact hdisj
      exact congrArg Subtype.val h1
    · have hmem : (s : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (((ζK⁻¹ : ↥(barX 3 N K)) : ↥(barX 3 N K)) :
          ↥N ⧸ GLAPPrimeCore 3 ↥N) * (s : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ ∈ barX 3 N K :=
        (Subgroup.mem_normalizer_iff.1 (hS₀ hsS) _).1 (ζK⁻¹).2
      let wK : ↥(barX 3 N K) := ⟨_, hmem⟩
      have h1 := hρ s' ζK⁻¹ wK rfl
      have h2 : (ζK : ↥N ⧸ GLAPPrimeCore 3 ↥N) * s * (ζK : ↥N ⧸ GLAPPrimeCore 3 ↥N)⁻¹ * s⁻¹ =
          ((ζK * wK : ↥(barX 3 N K)) : ↥N ⧸ GLAPPrimeCore 3 ↥N) := by
        simp [wK, mul_assoc]
      rw [h2, Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe (ψ _)]
      have h3 : ((ψ (ζK * wK) : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) =
          ζ * ρ s' * ζ⁻¹ * (ρ s')⁻¹ := by
        simp only [map_mul, Subgroup.coe_mul]
        rw [h1]
        simp [hψζ, mul_assoc]
      rw [h3]
      exact hζcomm.orderOf

end Perm

section Lift

theorem mem_normalizer_of_pow_three {Y : Type*} [Group Y] {H : Subgroup Y} {x : Y} (hx : x ^ 3 = 1)
    (h : ∀ w ∈ H, x * w * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨h w, fun hw => ?_⟩
  have h1 := h _ (h _ hw)
  have e : x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = w := by
    have hx' : x * (x * x) = 1 := by rw [← pow_three]; exact hx
    calc x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ = (x * (x * x)) * w * (x * (x * x))⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = w := by rw [hx']; group
  rw [e] at h1
  exact h1

theorem exists_order_three_lift {G : Type} [Group G] [Finite G] {N : Subgroup G} {x₂ : G}
    (hx₂N : x₂ ∈ N) {xb : ↥N ⧸ GLAPPrimeCore 3 ↥N}
    (hx₂ : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x₂, hx₂N⟩ = xb) (hxb : orderOf xb = 3) :
    ∃ (n' : ℕ) (x : G) (hxN : x ∈ N), x ∈ Subgroup.zpowers x₂ ∧ orderOf x = 3 ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x, hxN⟩ = xb ^ n' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpos : 0 < orderOf x₂ := orderOf_pos x₂
  obtain ⟨e, n', hn', hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 3 (by norm_num)
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hord
    omega
  have hxord : orderOf (x₂ ^ n') = 3 ^ e := by
    rw [orderOf_pow_of_dvd hn'0 (by rw [hord]; exact dvd_mul_left _ _), hord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'0)]
  have hxN : x₂ ^ n' ∈ N := N.pow_mem hx₂N n'
  set xN : ↥N := ⟨x₂ ^ n', hxN⟩ with hxNdef
  have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) xN = xb ^ n' := by
    have : xN = (⟨x₂, hx₂N⟩ : ↥N) ^ n' := Subtype.ext rfl
    rw [this, map_pow, hx₂]
  have hxNord : orderOf xN = 3 ^ e := by
    rw [← Subgroup.orderOf_coe xN]
    exact hxord
  have hcop : Nat.Coprime (orderOf xb) n' := by
    rw [hxb]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn'
  have hmkord : orderOf (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) xN) = 3 := by
    rw [hmk, Nat.Coprime.orderOf_pow hcop, hxb]
  have he1 : 1 ≤ e := by
    have h1 : 3 ∣ 3 ^ e := by
      have := orderOf_map_dvd (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) xN
      rw [hmkord, hxNord] at this
      exact this
    by_contra he
    have : e = 0 := by omega
    rw [this, pow_zero] at h1
    omega
  have hxb3 : xb ^ 3 = 1 := by
    have := pow_orderOf_eq_one xb
    rwa [hxb] at this
  have hcube : xN ^ 3 = 1 := by
    set z : ↥N := xN ^ 3 with hz
    have hzker : z ∈ GLAPPrimeCore 3 ↥N := by
      rw [← QuotientGroup.ker_mk' (GLAPPrimeCore 3 ↥N), MonoidHom.mem_ker, hz, map_pow, hmk,
        ← pow_mul, mul_comm, pow_mul, hxb3, one_pow]
    have hz1 : orderOf z ∣ 3 ^ (e - 1) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hz, ← pow_mul, show 3 * 3 ^ (e - 1) = 3 ^ e by
        rw [← pow_succ']; congr 1; omega, ← hxNord]
      exact pow_orderOf_eq_one xN
    have hz2 : orderOf z ∣ Nat.card (GLAPPrimeCore 3 ↥N) := by
      have := orderOf_dvd_natCard (⟨z, hzker⟩ : GLAPPrimeCore 3 ↥N)
      rwa [← Subgroup.orderOf_coe (⟨z, hzker⟩ : GLAPPrimeCore 3 ↥N)] at this
    have hcopV : Nat.Coprime (3 ^ (e - 1)) (Nat.card (GLAPPrimeCore 3 ↥N)) :=
      Nat.Coprime.pow_left _ CFSG.pPrimeCore_coprime_card
    have : orderOf z ∣ 1 := by
      have := Nat.dvd_gcd hz1 hz2
      rwa [hcopV.gcd_eq_one] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  have hx3 : (x₂ ^ n') ^ 3 = 1 := by
    have := congrArg (fun w : ↥N => (w : G)) hcube
    simpa using this
  have hx1 : x₂ ^ n' ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    have : 3 ^ e ≥ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) he1
    omega
  exact ⟨n', x₂ ^ n', hxN, ⟨n', by simp⟩, orderOf_eq_prime hx3 hx1, hmk⟩

end Lift

section Final

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129f
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129g
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (card_barX_of_isPGroup elemAbelian_barX)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129b

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D S F K : Subgroup G}

theorem alt_E5 (h128 : Lemma128Statement) (h23 : Lemma129e.Input23_5) (h121 : Prop121_corStatement)
    (h : Cex127 G m p B M E A N D) (hs : Setup2 M A N p S F K)
    (D' : AltData p N K F) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hr2 : CFSG.Open.pRank p F = 2) : 5 ≤ CFSG.Open.pRank p E := by
  have hp := prime_of h
  have hFA := alt_F_ne_A h23 h hs D'
  obtain ⟨hp3, hδ4⟩ := alt_p_three_delta_four h121 h hs D' hAK hFA
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 := ne_two_of h
  by_contra h5
  have hE4 : CFSG.Open.pRank 3 E ≤ 4 := by omega
  obtain ⟨hm1, htrans, a, haA, hAeq, hFa, σ, hσ3, hσsupp, hperm⟩ :=
    alt_structure h hs D' hAK hFA rfl hδ4
  have hn13 : D'.n = 13 := by
    have := D'.hn
    rw [hδ4, hm1, hr2] at this
    simpa using this
  have hAN := A_le_N h
  have hFA' := hs.F_le_A
  have hFN : F ≤ N := hFA'.trans hAN
  have hle := alt_le_K h hs D' hAK hFA rfl hδ4
  have hFK : barX 3 N F ≤ barX 3 N K := (barX_mono129 hFA').trans hle
  have hn11 := D'.hn11 (le_refl 3) hs.hr
  have hκself : ∀ f : ↥(barX 3 N F), D'.κ f = ⟨(f : ↥N ⧸ GLAPPrimeCore 3 ↥N), hFK f.2⟩ := by
    intro f
    apply impl_unique (by omega) D'.ψ
    intro x
    rw [← D'.hκ f x]
  have hFfix : ∀ g ∈ permImage D'.ψ (barX 3 N F), ∀ j ∈ D'.Ω₀, g j = j := by
    intro g hg j hj
    obtain ⟨x, hx, rfl⟩ := (mem_permImage D'.ψ).1 hg
    have h1 := D'.hfix ⟨(x : ↥N ⧸ GLAPPrimeCore 3 ↥N), hx⟩ j hj
    rw [hκself] at h1
    exact h1
  have hFel : IsElemAbelian 3 F := (A_el h).mono hFA'
  have hFcard : Nat.card (barX 3 N F) = 9 := by
    rw [card_barX_of_isPGroup hp hFN hFel.isPGroup, card_eq_pow_pRank hp hFel, hr2]
    norm_num
  have hA3 : CFSG.Open.pRank 3 A = 3 := by
    have h1 := card_A_of_ne hp hs hFA
    rw [card_eq_pow_pRank hp (A_el h), card_eq_pow_pRank hp hFel, hr2] at h1
    have h2 : (3 : ℕ) ^ CFSG.Open.pRank 3 A = 3 ^ 3 := by rw [h1]; norm_num
    exact (Nat.pow_right_injective hp.two_le) h2
  have haN : a ∈ N := hAN haA
  have hap : a ^ 3 = 1 := (A_el h).2 a haA
  have hFa' : ∀ f ∈ F, f * a = a * f := fun f hf => elemAbelian_comm (A_el h) (hFA' hf) haA
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (A0_inf_F_ne_bot h hs)
  have hyEA : (y : G) ∈ E ⊓ A := y.2.1
  have hyF : (y : G) ∈ F := y.2.2
  have hyN : (y : G) ∈ N := hAN hyEA.2
  have hybF : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨(y : G), hyN⟩ ∈ barX 3 N F :=
    ⟨⟨y, hyN⟩, (Subgroup.mem_subgroupOf).2 hyF, rfl⟩
  have hybA0 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨(y : G), hyN⟩ ∈ barX 3 N (E ⊓ A) :=
    ⟨⟨y, hyN⟩, (Subgroup.mem_subgroupOf).2 hyEA, rfl⟩
  have hAinj : ∀ u (huA : u ∈ A), QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨u, hAN huA⟩ = 1 →
      u = 1 := by
    intro u huA hu1
    have hinj := injective_barX_comp hp (A_el h).isPGroup hAN
    have : (⟨⟨u, hAN huA⟩, (Subgroup.mem_subgroupOf).2 huA⟩ : ↥(A.subgroupOf N)) = 1 :=
      hinj (by simpa using hu1)
    exact congrArg (fun w : ↥(A.subgroupOf N) => ((w : ↥N) : G)) this
  have hyb1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨(y : G), hyN⟩ ≠ 1 := fun h1 =>
    hy1 (Subtype.ext (hAinj y hyEA.2 h1))
  have habA : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩ ∈ barX 3 N A :=
    ⟨⟨a, haN⟩, (Subgroup.mem_subgroupOf).2 haA, rfl⟩
  have habK := hle habA
  have hperm' : permImage D'.ψ (Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩)) =
      Subgroup.zpowers σ := by
    rw [← barX_zpowers haN]
    exact hperm
  obtain ⟨xb, hxbK, hxbord, hxbcomm, hxbS⟩ := exists_x_zeta hn13 D'.ψ D'.Ω₀
    (by rw [D'.hΩ₀, hδ4]) hFK (isElemAbelian_barX hFel) hFcard hFfix htrans hybF hyb1 habK hσ3
    hσsupp hperm'
  have hSN : S ≤ N := hs.hS.le.trans h.hO
  have hS₂ : IsPGroup 2 ↥(barX 3 N S) :=
    Lemma129.isPGroup_barX ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hs.hS.le) hSN
  have hSF : ∀ s ∈ barX 3 N S, ∀ f ∈ barX 3 N F, s * f = f * s := by
    rintro _ ⟨⟨σ₁, hσ₁N⟩, hσ₁, rfl⟩ _ ⟨⟨f₁, hf₁N⟩, hf₁, rfl⟩
    have hσS : σ₁ ∈ S := (Subgroup.mem_subgroupOf).1 hσ₁
    have hfF : f₁ ∈ F := (Subgroup.mem_subgroupOf).1 hf₁
    exact mk_comm_of_comm hσ₁N hf₁N (Subgroup.mem_centralizer_iff.1 (hs.F_le_cent hfF) σ₁ hσS)
  obtain ⟨hSx, hSzeta⟩ := hxbS (barX 3 N S) hs.hSK hS₂ hSF
  obtain ⟨s, hsS, ζ, hζK, hζx, hord3⟩ := hSzeta hs.hKc
  have hxnorm : ∀ w ∈ barX 3 N (E ⊓ A), xb * w * xb⁻¹ ∈ barX 3 N (E ⊓ A) := by
    intro w hw
    obtain ⟨⟨x₀, hx₀N⟩, hx₀, rfl⟩ := hw
    have hx₀' : x₀ ∈ E ⊓ A := (Subgroup.mem_subgroupOf).1 hx₀
    obtain ⟨f, hfF, j, hxj⟩ := exists_mul_pow_of_mem_sup hp.pos hap hFa' (hAeq ▸ hx₀'.2)
    have hfN : f ∈ N := hFN hfF
    have hπ : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x₀, hx₀N⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨f, hfN⟩ *
          (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩) ^ j := by
      have : (⟨x₀, hx₀N⟩ : ↥N) = ⟨f, hfN⟩ * ⟨a, haN⟩ ^ j := Subtype.ext hxj
      rw [this, map_mul, map_pow]
    have hfb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨f, hfN⟩ ∈ barX 3 N F :=
      ⟨⟨f, hfN⟩, (Subgroup.mem_subgroupOf).2 hfF, rfl⟩
    have hc := hxbcomm _ hfb j
    rw [← hπ] at hc
    have hc' := (Subgroup.zpowers_le.2 hybA0) hc
    have hw0 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x₀, hx₀N⟩ ∈ barX 3 N (E ⊓ A) :=
      ⟨⟨x₀, hx₀N⟩, hx₀, rfl⟩
    have := (barX 3 N (E ⊓ A)).mul_mem hc' hw0
    simpa [mul_assoc] using this
  have hxb3 : xb ^ 3 = 1 := by
    have := pow_orderOf_eq_one xb
    rwa [hxbord] at this
  have hxbN : xb ∈ Subgroup.normalizer (barX 3 N (E ⊓ A) : Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) :=
    mem_normalizer_of_pow_three hxb3 hxnorm
  have hA0N : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hA0p : IsPGroup 3 ↥(E ⊓ A) := ((A_el h).mono inf_le_right).isPGroup
  obtain ⟨⟨x₂, hx₂N⟩, hx₂mem, hx₂mk⟩ := normalizer_barX_le hp hA0p hA0N hxbN
  have hx₂nor : x₂ ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    (Subgroup.mem_subgroupOf).1 hx₂mem
  have hcoreE : GLBCore 3 2 E ≤ M := (uniq_E h).clause_d
  have hx₂M : x₂ ∈ M := hcoreE (le_sSup (show Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∈
    {N' | ∃ Q : Subgroup G, Q ≤ E ∧ 2 ≤ CFSG.Open.pRank 3 Q ∧
      N' = Subgroup.normalizer (Q : Set G)} from ⟨E ⊓ A, inf_le_left, two_le_rank_inf h, rfl⟩)
    hx₂nor)
  obtain ⟨n', x, hxN, hxz, hxord3, hxmk⟩ := exists_order_three_lift hx₂N hx₂mk hxbord
  have hxM : x ∈ M := (Subgroup.zpowers_le.2 hx₂M) hxz
  have h128x := h128 h.toSec11 hE4 hA3 hxM hxord3
  have hd : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord3]; norm_num)
  have hLN : pCoreOf 2 M ≤ N := h.hO
  have hdL : x ∈ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hxM
  have hlift1 := barX_inf_centralizer hp (M := N) (L := pCoreOf 2 M) hxN hLN hdL hd
  have hlift2 := barX_inf_centralizer hp (M := N) (L := N) hxN le_rfl
    (Subgroup.le_normalizer hxN) hd
  have hsx : s * QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x, hxN⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x, hxN⟩ * s := by
    rw [hxmk]
    exact (Commute.pow_right (show Commute s xb from hSx s hsS) n').eq
  have hζx' : ζ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x, hxN⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨x, hxN⟩ * ζ := by
    rw [hxmk]
    exact (Commute.pow_right (show Commute ζ xb from hζx) n').eq
  have hs₁ : s ∈ barX 3 N (pCoreOf 2 M ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hlift1]
    exact ⟨barX_mono129 hs.hS.le hsS, Subgroup.mem_centralizer_singleton_iff.2 hsx⟩
  have hζ₁ : ζ ∈ barX 3 N (N ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hlift2]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 hζx'⟩
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective ζ
    exact ⟨z, (Subgroup.mem_subgroupOf).2 z.2, hz⟩
  obtain ⟨⟨s₁, hs₁N⟩, hs₁mem, hs₁mk⟩ := hs₁
  obtain ⟨⟨ζ₁, hζ₁N⟩, hζ₁mem, hζ₁mk⟩ := hζ₁
  have hs₁' : s₁ ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({x} : Set G) :=
    (Subgroup.mem_subgroupOf).1 hs₁mem
  have hζ₁' : ζ₁ ∈ N ⊓ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_subgroupOf).1 hζ₁mem
  have hs₁O : s₁ ∈ pCoreOf 2 (Cg x) := h128x hs₁'
  have hζ₁nor : ζ₁ ∈ Subgroup.normalizer ((pCoreOf 2 (Cg x) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Cg x) hζ₁'.2
  have hc : ζ₁ * s₁ * ζ₁⁻¹ * s₁⁻¹ ∈ pCoreOf 2 (Cg x) := by
    refine (pCoreOf 2 (Cg x)).mul_mem ?_ ((pCoreOf 2 (Cg x)).inv_mem hs₁O)
    exact (Subgroup.mem_normalizer_iff.1 hζ₁nor s₁).1 hs₁O
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Cg x)) ⟨_, hc⟩
  have h1 : (⟨ζ₁, hζ₁N⟩ * ⟨s₁, hs₁N⟩ * ⟨ζ₁, hζ₁N⟩⁻¹ * ⟨s₁, hs₁N⟩⁻¹ : ↥N) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h2 := congrArg (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N)) h1
  rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, hζ₁mk, hs₁mk, map_one] at h2
  have h3 : 3 ∣ 2 ^ k := hord3 ▸ orderOf_dvd_of_pow_eq_one h2
  have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129j

end
