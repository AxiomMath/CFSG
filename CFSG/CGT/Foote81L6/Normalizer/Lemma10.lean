module

public import CFSG.CGT.Foote81L6.Normalizer.Lemma8
public import CFSG.CGT.Foote81L6.Normalizer.Lemma9

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin Equiv

variable {V X : Type*} [CommGroup V] [Group X]

private theorem tv_apply_comm_eq {t g : MulAut V} {w : V} (ht : IsTransvectionWith t w)
    (ht1 : t ≠ 1) (hg : g * t = t * g) (v : V) : t (g v * v⁻¹) = g v * v⁻¹ := by
  have hgw : g w = w := B1.tv_comm_centre ht ht1 hg
  have htg : t (g v) = g (t v) := by
    have := congrArg (fun f : MulAut V => f v) hg
    simp only [MulAut.mul_apply] at this
    exact this.symm
  rw [map_mul, map_inv, htg]
  rcases ht.2 v with h | h
  · rw [h]
  · rw [h, map_mul, hgw]
    group

theorem eq_one_of_commute_of_fix [Finite X] (hV : ∀ v : V, v * v = 1) {ρ : X →* MulAut V}
    (hρ : Function.Injective ρ) {d₀ d₁ : X} (hd₀ : IsTransvection (ρ d₀))
    (hd₁ : IsTransvection (ρ d₁)) {k : X} (hk : Odd (orderOf k)) (hk₀ : k * d₀ = d₀ * k)
    (hk₁ : k * d₁ = d₁ * k) (hfix : ∀ v : V, ρ d₀ v = v → ρ d₁ v = v → ρ k v = v) : k = 1 := by
  obtain ⟨h01, w₀, hw₀⟩ := hd₀
  obtain ⟨h11, w₁, hw₁⟩ := hd₁
  have hc : ∀ v : V, ρ k (ρ k v * v⁻¹) = ρ k v * v⁻¹ := fun v =>
    hfix _ (tv_apply_comm_eq hw₀ h01 (by rw [← map_mul, ← map_mul, hk₀]) v)
      (tv_apply_comm_eq hw₁ h11 (by rw [← map_mul, ← map_mul, hk₁]) v)
  have hρk : ρ k = 1 := by
    refine MulEquiv.ext fun v => ?_
    set c := ρ k v * v⁻¹ with hcdef
    have hkv : ρ k v = v * c := by rw [hcdef, mul_comm v, inv_mul_cancel_right]
    have hkc : ρ k c = c := hc v
    have hpow : ∀ n : ℕ, ρ (k ^ n) v = v * c ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, hkv, map_pow, hkc, pow_succ]
        group
    obtain ⟨m, hm⟩ := hk
    have h1 : v * c ^ (orderOf k) = v := by
      rw [← hpow, pow_orderOf_eq_one, map_one, MulAut.one_apply]
    have hc1 : c ^ (orderOf k) = 1 := by
      have := congrArg (fun u => v⁻¹ * u) h1
      simpa using this
    have hcc : c ^ 2 = 1 := by rw [pow_two]; exact hV c
    rw [hm, pow_succ, pow_mul, hcc, one_pow, one_mul] at hc1
    show ρ k v = v
    rw [hkv, hc1, mul_one]
  exact hρ (hρk.trans (map_one ρ).symm)

theorem exists_mul_of_hasNormalPComplement [Finite X] (D : Sylow 2 X)
    (hnc : HasNormalPComplement 2 X) (g : X) :
    ∃ s ∈ (D : Subgroup X), ∃ o ∈ pPrimeCore 2 X, g = s * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 X hnc
  set π := QuotientGroup.mk' (pPrimeCore 2 X)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Dbar : Sylow 2 (X ⧸ pPrimeCore 2 X) := D.mapSurjective hπs
  have htop : (⊤ : Subgroup (X ⧸ pPrimeCore 2 X)) = Dbar :=
    Dbar.is_maximal' (hq.to_subgroup ⊤) le_top
  have hg : π g ∈ (Dbar : Subgroup (X ⧸ pPrimeCore 2 X)) := by
    rw [← htop]
    exact Subgroup.mem_top _
  obtain ⟨s, hs, hsg⟩ := hg
  refine ⟨s, hs, s⁻¹ * g, QuotientGroup.eq.mp hsg, by group⟩

namespace TvHyp

variable {D : Sylow 2 X} {d₀ d₁ : X} {ρ : X →* MulAut V}

theorem normal_oddCentralizer [Finite X] (h : TvHyp ρ D d₀ d₁)
    (hnc : HasNormalPComplement 2 X) {x₀ x₁ : X} (hP : IsLemma8Pair d₀ d₁ x₀ x₁) :
    (oddCentralizer d₀ d₁).Normal := by
  have hO := (inferInstance : (pPrimeCore 2 X).Normal)
  refine ⟨fun k hk g => ?_⟩
  obtain ⟨hkO, hk₀, hk₁⟩ := mem_oddCentralizer.mp hk
  obtain ⟨s, hs, o, ho, rfl⟩ := exists_mul_of_hasNormalPComplement D hnc g
  obtain ⟨a, b, k', hk', rfl⟩ := hP.decomp o ho
  obtain ⟨hk'O, hk'₀, hk'₁⟩ := mem_oddCentralizer.mp hk'
  have hx₀ : Commute (x₀ ^ a) k := (Commute.zpow_left (hP.central₀ k hkO).symm a)
  have hx₁ : Commute (x₁ ^ b) k := (Commute.zpow_left (hP.central₁ k hkO).symm b)
  have e1 : x₀ ^ a * x₁ ^ b * k' * k * (x₀ ^ a * x₁ ^ b * k')⁻¹ = k' * k * k'⁻¹ := by
    have h1 : x₁ ^ b * (k' * k * k'⁻¹) * (x₁ ^ b)⁻¹ = k' * k * k'⁻¹ := by
      have hc : Commute (x₁ ^ b) (k' * k * k'⁻¹) :=
        Commute.zpow_left (hP.central₁ _ (hO.conj_mem k hkO k')).symm b
      rw [hc.eq]; group
    have h0 : x₀ ^ a * (k' * k * k'⁻¹) * (x₀ ^ a)⁻¹ = k' * k * k'⁻¹ := by
      have hc : Commute (x₀ ^ a) (k' * k * k'⁻¹) :=
        Commute.zpow_left (hP.central₀ _ (hO.conj_mem k hkO k')).symm a
      rw [hc.eq]; group
    calc x₀ ^ a * x₁ ^ b * k' * k * (x₀ ^ a * x₁ ^ b * k')⁻¹
        = x₀ ^ a * (x₁ ^ b * (k' * k * k'⁻¹) * (x₁ ^ b)⁻¹) * (x₀ ^ a)⁻¹ := by group
      _ = k' * k * k'⁻¹ := by rw [h1, h0]
  set k'' := k' * k * k'⁻¹ with hk''
  have hk''K : k'' ∈ oddCentralizer d₀ d₁ := by
    refine mem_oddCentralizer.mpr ⟨hO.conj_mem k hkO k', ?_, ?_⟩
    · calc k' * k * k'⁻¹ * d₀ = k' * k * (d₀ * k'⁻¹) := by
            rw [mul_assoc, show k'⁻¹ * d₀ = d₀ * k'⁻¹ by
              calc k'⁻¹ * d₀ = k'⁻¹ * (d₀ * k') * k'⁻¹ := by group
                _ = k'⁻¹ * (k' * d₀) * k'⁻¹ := by rw [hk'₀]
                _ = d₀ * k'⁻¹ := by group]
        _ = k' * (k * d₀) * k'⁻¹ := by group
        _ = k' * (d₀ * k) * k'⁻¹ := by rw [hk₀]
        _ = (k' * d₀) * k * k'⁻¹ := by group
        _ = d₀ * (k' * k * k'⁻¹) := by rw [hk'₀]; group
    · calc k' * k * k'⁻¹ * d₁ = k' * k * (d₁ * k'⁻¹) := by
            rw [mul_assoc, show k'⁻¹ * d₁ = d₁ * k'⁻¹ by
              calc k'⁻¹ * d₁ = k'⁻¹ * (d₁ * k') * k'⁻¹ := by group
                _ = k'⁻¹ * (k' * d₁) * k'⁻¹ := by rw [hk'₁]
                _ = d₁ * k'⁻¹ := by group]
        _ = k' * (k * d₁) * k'⁻¹ := by group
        _ = k' * (d₁ * k) * k'⁻¹ := by rw [hk₁]
        _ = (k' * d₁) * k * k'⁻¹ := by group
        _ = d₁ * (k' * k * k'⁻¹) := by rw [hk'₁]; group
  obtain ⟨hs0, hs1⟩ : (s⁻¹ * d₀ * s = d₀ ∨ s⁻¹ * d₀ * s = d₁) ∧
      (s⁻¹ * d₁ * s = d₀ ∨ s⁻¹ * d₁ * s = d₁) := by
    have hsD : s⁻¹ ∈ (D : Subgroup X) := (D : Subgroup X).inv_mem hs
    constructor
    · have := h.conj_eq (g := s⁻¹) (by
        rw [inv_inv]
        exact (D : Subgroup X).mul_mem ((D : Subgroup X).mul_mem hsD h.mem₀) hs)
      simpa [inv_inv] using this
    · have := h.conj_eq₁ (g := s⁻¹) (by
        rw [inv_inv]
        exact (D : Subgroup X).mul_mem ((D : Subgroup X).mul_mem hsD h.mem₁) hs)
      simpa [inv_inv] using this
  obtain ⟨hk''O, hk''₀, hk''₁⟩ := mem_oddCentralizer.mp hk''K
  have hcommd : ∀ {d : X}, (s⁻¹ * d * s = d₀ ∨ s⁻¹ * d * s = d₁) →
      s * k'' * s⁻¹ * d = d * (s * k'' * s⁻¹) := by
    intro d hd
    have hk''d : k'' * (s⁻¹ * d * s) = (s⁻¹ * d * s) * k'' := by
      rcases hd with h1 | h1 <;> rw [h1]
      · exact hk''₀
      · exact hk''₁
    calc s * k'' * s⁻¹ * d = s * (k'' * (s⁻¹ * d * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * d * s) * k'') * s⁻¹ := by rw [hk''d]
      _ = d * (s * k'' * s⁻¹) := by group
  have e2 : s * (x₀ ^ a * x₁ ^ b * k') * k * (s * (x₀ ^ a * x₁ ^ b * k'))⁻¹ =
      s * k'' * s⁻¹ := by
    rw [← e1]
    group
  rw [e2]
  exact mem_oddCentralizer.mpr ⟨hO.conj_mem k'' hk''O s, hcommd hs0, hcommd hs1⟩

theorem transvection₁ (h : TvHyp ρ D d₀ d₁) : IsTransvection (ρ d₁) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h.isConj₁
  rw [map_mul, map_mul, map_inv]
  exact B1.isTransvection_conj h.transvection (ρ c)

end TvHyp

theorem lemma8_improved [Finite V] [Finite X] (hV : ∀ v : V, v * v = 1) {ρ : X →* MulAut V}
    (hρ : Function.Injective ρ) {d₀ d₁ : X} {b₀ b₁ : V} (hd₀ : IsTransvectionWith (ρ d₀) b₀)
    (hd₀1 : ρ d₀ ≠ 1) (hd₁ : IsTransvectionWith (ρ d₁) b₁) (hd₁1 : ρ d₁ ≠ 1) (hb : b₀ ≠ b₁)
    (hcomm : d₀ * d₁ = d₁ * d₀) (hL3 : ∀ g : X, ρ g b₀ ≠ b₀ * b₁)
    (hL10 : ∀ k : X, Odd (orderOf k) → k * d₀ = d₀ * k → k * d₁ = d₁ * k →
      ∀ v : V, ρ d₀ v = v → ρ d₁ v = v → ρ k v = v) :
    ∃ x₀ x₁ : X, x₀ ^ 3 = 1 ∧ x₁ ^ 3 = 1 ∧ d₀ * x₀ * d₀⁻¹ = x₀⁻¹ ∧ d₁ * x₁ * d₁⁻¹ = x₁⁻¹ ∧
      x₁ * d₀ = d₀ * x₁ ∧ x₀ * d₁ = d₁ * x₀ ∧ x₀ * x₁ = x₁ * x₀ ∧
      Subgroup.zpowers x₀ ⊓ Subgroup.zpowers x₁ = ⊥ ∧
      pPrimeCore 2 X = Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ := by
  obtain ⟨x₀, x₁, hP, hc₁, hc₀, huniq⟩ := lemma8 hV hρ hd₀ hd₀1 hd₁ hd₁1 hb hcomm hL3
  have hK : ∀ k ∈ oddCentralizer d₀ d₁, k = 1 := by
    intro k hk
    obtain ⟨hkO, hk₀, hk₁⟩ := mem_oddCentralizer.mp hk
    exact eq_one_of_commute_of_fix hV hρ ⟨hd₀1, b₀, hd₀⟩ ⟨hd₁1, b₁, hd₁⟩
      (odd_orderOf_of_mem_pPrimeCore hkO) hk₀ hk₁ (hL10 k (odd_orderOf_of_mem_pPrimeCore hkO) hk₀ hk₁)
  refine ⟨x₀, x₁, hP.pow₀, hP.pow₁, hP.inv₀, hP.inv₁, hc₁, hc₀, (hP.central₀ x₁ hP.mem₁).symm,
    ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨hg0, hg1⟩
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hg0
    obtain ⟨b, hb'⟩ := Subgroup.mem_zpowers_iff.mp hg1
    have h1 : x₀ ^ a * x₁ ^ (-b) * 1 = 1 := by rw [ha, zpow_neg, hb', mul_one, mul_inv_cancel]
    obtain ⟨h2, -, -⟩ := huniq a (-b) 1 (oddCentralizer d₀ d₁).one_mem h1
    rw [Subgroup.mem_bot, ← ha, h2]
  · apply le_antisymm
    · intro o ho
      obtain ⟨a, b, k, hk, rfl⟩ := hP.decomp o ho
      rw [hK k hk, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x₀ a))
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers x₁ b))
    · exact sup_le (Subgroup.zpowers_le.mpr hP.mem₀) (Subgroup.zpowers_le.mpr hP.mem₁)

theorem IsSymDirect.pPrimeCore_eq_bot [Finite V] [Finite X] {d₀ d₁ : X} {n : ℕ} [NeZero n]
    {φ : X →* Perm (Fin n)} (hφ : IsSymDirect d₀ d₁ φ) (hV : ∀ v : V, v * v = 1)
    {ρ : X →* MulAut V} (hρ : Function.Injective ρ) (hd₀ : IsTransvection (ρ d₀))
    (hd₁ : IsTransvection (ρ d₁))
    (hL10 : ∀ k : X, Odd (orderOf k) → k * d₀ = d₀ * k → k * d₁ = d₁ * k →
      ∀ v : V, ρ d₀ v = v → ρ d₁ v = v → ρ k v = v) :
    pPrimeCore 2 X = ⊥ := by
  rw [eq_bot_iff]
  intro o ho
  obtain ⟨h0, h1⟩ := hφ.commute_of_mem_pPrimeCore ho
  exact (Subgroup.mem_bot).mpr (eq_one_of_commute_of_fix hV hρ hd₀ hd₁
    (odd_orderOf_of_mem_pPrimeCore ho) h0 h1 (hL10 o (odd_orderOf_of_mem_pPrimeCore ho) h0 h1))

section Type0

variable {V X : Type} [CommGroup V] [Finite V] [Group X] [Finite X] {ρ : X →* MulAut V}
  {D : Sylow 2 X} {d₀ d₁ : X}

theorem TvHyp.lemma9_improved (h : TvHyp ρ D d₀ d₁) (hnc : ¬ HasNormalPComplement 2 X)
    (hHig : HigmanHyp)
    (hL10 : ∀ k : X, Odd (orderOf k) → k * d₀ = d₀ * k → k * d₁ = d₁ * k →
      ∀ v : V, ρ d₀ v = v → ρ d₁ v = v → ρ k v = v) :
    pPrimeCore 2 X = ⊥ ∧
      ((∃ e : X ≃* Perm (Fin 4), e d₀ = swap 0 1 ∧ e d₁ = swap 2 3) ∨
        (∃ e : X ≃* Perm (Fin 5), e d₀ = swap 0 1 ∧ e d₁ = swap 2 3)) := by
  have hbij : ∀ {n : ℕ} [NeZero n] {φ : X →* Perm (Fin n)}, IsSymDirect d₀ d₁ φ →
      pPrimeCore 2 X = ⊥ ∧ ∃ e : X ≃* Perm (Fin n), e d₀ = swap 0 1 ∧ e d₁ = swap 2 3 := by
    intro n _ φ hφ
    have hO := hφ.pPrimeCore_eq_bot h.sq_eq_one h.injective h.transvection h.transvection₁ hL10
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hO]
    exact ⟨hO, MulEquiv.ofBijective φ ⟨hinj, hφ.surjective⟩, hφ.map₀, hφ.map₁⟩
  rcases h.isSymDirect hnc hHig with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · obtain ⟨hO, he⟩ := hbij hφ
    exact ⟨hO, Or.inl he⟩
  · obtain ⟨hO, he⟩ := hbij hφ
    exact ⟨hO, Or.inr he⟩

theorem TvHyp.lemma10 (h : TvHyp ρ D d₀ d₁) (hHig : HigmanHyp)
    (hL1 : Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
      Subgroup.centralizer ({d₁} : Set X)) = 1 ∨
      Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
        Subgroup.centralizer ({d₁} : Set X)) = 3)
    {P : Subgroup X} (hP3 : Nat.card P = 3) (hP₀ : ∀ p ∈ P, p * d₀ = d₀ * p)
    (hP₁ : ∀ p ∈ P, p * d₁ = d₁ * p) :
    P.Normal ∧ ∀ g : X, ∀ v ∈ commV (P.map ρ), ρ g v ∈ commV (P.map ρ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPodd : Odd (Nat.card P) := by rw [hP3]; decide
  have hnormal : P.Normal := by
    by_cases hnc : HasNormalPComplement 2 X
    · have hPO : P ≤ pPrimeCore 2 X := by
        intro p hp
        have hq := CFSG.isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 X hnc
        obtain ⟨k, hk⟩ := hq (QuotientGroup.mk p)
        have hodd : Odd (orderOf (QuotientGroup.mk p : X ⧸ pPrimeCore 2 X)) :=
          (hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hp)).of_dvd_nat
            (orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 X)) p)
        have hk' : (QuotientGroup.mk p : X ⧸ pPrimeCore 2 X) ^ 2 ^ k = 1 := hk
        exact (QuotientGroup.eq_one_iff p).mp (eq_one_of_pow_two_pow_of_odd hk' hodd)
      obtain ⟨x₀, x₁, hpair⟩ := exists_isLemma8Pair h.sq_eq_one h.injective h.transvection
        h.transvection₁ h.dihedral_facts.1
      have hPK : P ≤ oddCentralizer d₀ d₁ := fun p hp =>
        mem_oddCentralizer.mpr ⟨hPO hp, hP₀ p hp, hP₁ p hp⟩
      have hK13 : Nat.card (oddCentralizer d₀ d₁) = 1 ∨
          Nat.card (oddCentralizer d₀ d₁) = 3 := hL1
      have hPeq : P = oddCentralizer d₀ d₁ :=
        Subgroup.eq_of_le_of_card_ge hPK (by rcases hK13 with h1 | h1 <;> omega)
      rw [hPeq]
      exact h.normal_oddCentralizer hnc hpair
    · obtain ⟨-, -, -, h3⟩ := h.lemma9 hnc hHig hPodd hP₀ hP₁ hL1
      rw [h3 hP3]
      infer_instance
  refine ⟨hnormal, fun g v hv => ?_⟩
  rw [commV_eq_commSub] at hv ⊢
  refine B1.commSub_smul_mem (M := ⊤) (M' := ⊤) (ρ g) (fun z hz => ?_)
    (fun _ _ => Subgroup.mem_top _) v hv
  obtain ⟨p, hp, rfl⟩ := hz
  exact ⟨g * p * g⁻¹, hnormal.conj_mem p hp g, by simp [map_mul, map_inv]⟩

end Type0

end CFSG.CGT.Foote81L6.Normalizer
