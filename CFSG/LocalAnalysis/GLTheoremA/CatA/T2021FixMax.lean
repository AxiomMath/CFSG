module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021Facts
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Quot
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Lift
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015

variable {H : Type} [Group H] [Finite H]

theorem t2021Fix_odd_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Odd (Nat.card (Subgroup.center (ppQuot p H))) := by
  have hcore : CFSG.pPrimeCore p (ppQuot p H) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (ppQuot p H)) 2 h2
  have hzn : (Subgroup.zpowers (z : ppQuot p H)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 z.2 hx) g, mul_inv_cancel_right]
    exact hx
  have hzc : Nat.Coprime p (Nat.card (Subgroup.zpowers (z : ppQuot p H))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have hbot := (CFSG.pPrimeCore_eq_bot_iff.1 hcore) _ hzn hzc
  have hz1 : (z : ppQuot p H) = 1 := by
    have : (z : ppQuot p H) ∈ Subgroup.zpowers (z : ppQuot p H) := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  norm_num at hz

theorem t2021Fix_map_eq {G : Type} [Group G] [Finite G] (φ : MulAut G) {T : Subgroup G}
    (hT : ∀ t ∈ T, φ t ∈ T) : T.map φ.toMonoidHom = T :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨t, ht, rfl⟩; exact hT t ht)
    (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge

theorem t2021Fix_normalizer_inv {G : Type} [Group G] [Finite G] (φ : MulAut G) {T : Subgroup G}
    (hT : ∀ t ∈ T, φ t ∈ T) {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    φ x ∈ Subgroup.normalizer (T : Set G) := by
  have h := Subgroup.le_normalizer_map (H := T) φ.toMonoidHom ⟨x, hx, rfl⟩
  rwa [t2021Fix_map_eq φ hT] at h

theorem t2021Fix_sylow_of_max {p : ℕ} (hp : p.Prime) {𝔅 : Type} [Group 𝔅] (ψ : 𝔅 →* MulAut H)
    (h𝔅 : IsPGroup p 𝔅) {T X : Subgroup H} (hT2 : IsPGroup 2 T)
    (hTinv : ∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T)
    (hTmax : ∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T)
    (hTX : T ≤ X) (hXinv : ∀ g : 𝔅, ∀ x ∈ X, ψ g x ∈ X) (hX : ¬ p ∣ Nat.card X) :
    Nat.card T = 2 ^ (Nat.card X).factorization 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup H := X ⊓ Subgroup.normalizer (T : Set H) with hM
  have hMinv : ∀ g : 𝔅, ∀ x ∈ M, ψ g x ∈ M := fun g x hx =>
    ⟨hXinv g x hx.1, t2021Fix_normalizer_inv (ψ g) (hTinv g) hx.2⟩
  have hMp : ¬ p ∣ Nat.card M := fun h => hX (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hTM : T ≤ M := le_inf hTX Subgroup.le_normalizer
  obtain ⟨P, hP⟩ := t2021TD4Lift_exists_sylow ψ (r := p) (q := 2) h𝔅 hMinv hMp
  have hTn : (T.subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hm : (m : H) ∈ Subgroup.normalizer (T : Set H) := m.2.2
    simpa using (Subgroup.mem_normalizer_iff.1 hm (n : H)).1 hn
  have hTP : T.subgroupOf M ≤ (P : Subgroup ↥M) := by
    haveI : (Subgroup.comap M.subtype T).Normal := hTn
    exact (hT2.comap_of_injective M.subtype M.subtype_injective).le_sylow_of_normal P
  set P' : Subgroup H := (P : Subgroup ↥M).map M.subtype with hP'
  have hTP' : T ≤ P' := by
    intro t ht
    exact ⟨⟨t, hTM ht⟩, hTP (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map M.subtype
  have hP'inv : ∀ g : 𝔅, ∀ t ∈ P', ψ g t ∈ P' := by
    rintro g _ ⟨x, hx, rfl⟩
    exact hP g x hx
  have hP'T : P' = T := hTmax P' hP'2 hP'inv hTP'
  have hcardT : Nat.card T = 2 ^ (Nat.card M).factorization 2 := by
    rw [← hP'T, hP', Subgroup.card_map_of_injective M.subtype_injective]
    exact P.card_eq_multiplicity
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hTXdvd : 2 ^ n ∣ Nat.card X := hn ▸ Subgroup.card_dvd_of_le hTX
  have hle : n ≤ (Nat.card X).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hTXdvd
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hdvd : 2 ^ (n + 1) ∣ Nat.card ↥X :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').2 hlt
    have hcardTX : Nat.card (T.subgroupOf X) = 2 ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hn]
    have hNdvd := Sylow.prime_pow_dvd_card_normalizer hdvd hcardTX
    have hNM : Nat.card (Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)) =
        Nat.card M := by
      have hmap : (Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)).map X.subtype = M := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨x.2, ?_⟩
          show (x : H) ∈ Subgroup.normalizer (T : Set H)
          rw [Subgroup.mem_normalizer_iff]
          intro h
          by_cases hh : h ∈ X
          · have := (Subgroup.mem_normalizer_iff.1 hx) ⟨h, hh⟩
            simp only [Subgroup.mem_subgroupOf] at this
            simpa using this
          · constructor
            · intro ht
              exact absurd (hTX ht) hh
            · intro ht
              exfalso
              apply hh
              have h1 : (x : H) * h * (x : H)⁻¹ ∈ X := hTX ht
              have h2 : (x : H)⁻¹ * ((x : H) * h * (x : H)⁻¹) * (x : H) ∈ X :=
                X.mul_mem (X.mul_mem (X.inv_mem x.2) h1) x.2
              simpa [mul_assoc] using h2
        · rintro ⟨hyX, hyN⟩
          refine ⟨⟨y, hyX⟩, ?_, rfl⟩
          show (⟨y, hyX⟩ : ↥X) ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup ↥X) : Set ↥X)
          rw [Subgroup.mem_normalizer_iff]
          intro h
          simp only [Subgroup.mem_subgroupOf]
          simpa using (Subgroup.mem_normalizer_iff.1 hyN (h : H))
      rw [← hmap, Subgroup.card_map_of_injective X.subtype_injective]
    rw [hNM] at hNdvd
    have h2M := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hNdvd
    have hfac : (Nat.card M).factorization 2 = n := by
      have := hcardT.symm.trans hn
      exact Nat.pow_right_injective (le_refl 2) this
    omega
  · rw [hn, heq]

theorem t2021Fix_maxQ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {𝔅 : Type} [Group 𝔅] (ψ : 𝔅 →* MulAut H)
    (ψQ : 𝔅 → MulAut (ppQuot p H))
    (hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l))
    (h𝔅 : IsPGroup p 𝔅) {T : Subgroup H} (hT2 : IsPGroup 2 T)
    (hTinv : ∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T)
    (hTmax : ∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T)
    {V : Subgroup (ppQuot p H)} (hV2 : IsPGroup 2 V) (hVinv : ∀ g : 𝔅, ∀ v ∈ V, ψQ g v ∈ V)
    (hTV : T.map (QuotientGroup.mk' (GLAPPrimeCore p H)) ≤ V) :
    V = T.map (QuotientGroup.mk' (GLAPPrimeCore p H)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* ppQuot p H := QuotientGroup.mk' (GLAPPrimeCore p H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set X : Subgroup H := V.comap π with hX
  have hTX : T ≤ X := fun t ht => hTV ⟨t, ht, rfl⟩
  have hXinv : ∀ g : 𝔅, ∀ x ∈ X, ψ g x ∈ X := by
    intro g x hx
    show π (ψ g x) ∈ V
    rw [hπ, QuotientGroup.mk'_apply, ← hψQ]
    exact hVinv g _ hx
  have hXmap : X.map π = V := Subgroup.map_comap_eq_self_of_surjective hπs V
  have hXp : ¬ p ∣ Nat.card X := by
    have h1 : Nat.card ↥X = Nat.card (π.comp X.subtype).range * Nat.card (π.comp X.subtype).ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (π.comp X.subtype)).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hfr : (π.comp X.subtype).range = V := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hXmap]
    have hkdvd : Nat.card (π.comp X.subtype).ker ∣ Nat.card (GLAPPrimeCore p H) := by
      have hle : (π.comp X.subtype).ker.map X.subtype ≤ GLAPPrimeCore p H := by
        rintro _ ⟨k, hk, rfl⟩
        have hk' : X.subtype k ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hk)
        rwa [hπ, QuotientGroup.ker_mk'] at hk'
      have h2 := Subgroup.card_dvd_of_le hle
      rwa [Subgroup.card_map_of_injective X.subtype_injective] at h2
    have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p H) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    rw [h1, hfr, Nat.Prime.dvd_mul hp]
    rintro (h | h)
    · obtain ⟨n, hn⟩ := hV2.exists_card_eq
      rw [hn] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hN (h.trans hkdvd)
  have hTsyl := t2021Fix_sylow_of_max hp ψ h𝔅 hT2 hTinv hTmax hTX hXinv hXp
  have hcardTX : Nat.card (T.subgroupOf X) = 2 ^ (Nat.card ↥X).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hTsyl]
  set TX : Sylow 2 ↥X := Sylow.ofCard (T.subgroupOf X) hcardTX with hTXdef
  have hfX : ∀ x : ↥X, π (x : H) ∈ V := fun x => x.2
  set fX : ↥X →* ↥V := (π.comp X.subtype).codRestrict V hfX with hfXdef
  have hfXs : Function.Surjective fX := by
    intro v
    obtain ⟨x, hx, hxv⟩ : (v : ppQuot p H) ∈ X.map π := hXmap.symm ▸ v.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxv⟩
  have htop : ((TX.mapSurjective hfXs : Sylow 2 ↥V) : Subgroup ↥V) = ⊤ :=
    ((TX.mapSurjective hfXs).3 (IsPGroup.of_equiv hV2 Subgroup.topEquiv.symm) le_top).symm
  refine le_antisymm ?_ hTV
  intro v hv
  have hv' : (⟨v, hv⟩ : ↥V) ∈ ((TX.mapSurjective hfXs : Sylow 2 ↥V) : Subgroup ↥V) := by
    rw [htop]; trivial
  rw [Sylow.coe_mapSurjective] at hv'
  obtain ⟨x, hx, hxv⟩ := hv'
  have hxT : (x : H) ∈ T := by
    have : x ∈ T.subgroupOf X := by rw [hTXdef, Sylow.coe_ofCard] at hx; exact hx
    exact Subgroup.mem_subgroupOf.1 this
  exact ⟨x, hxT, congrArg Subtype.val hxv⟩

theorem t2021Fix_maxS {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {𝔅 : Type} [Group 𝔅] (ψ : 𝔅 →* MulAut H)
    (ψQ : 𝔅 → MulAut (ppQuot p H))
    (hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l))
    (ψS : 𝔅 → MulAut (psimpleOf p H))
    (hψS : ∀ (g : 𝔅) (x : ppQuot p H), ψS g (QuotientGroup.mk x) = QuotientGroup.mk (ψQ g x))
    (h𝔅 : IsPGroup p 𝔅) {T : Subgroup H} (hT2 : IsPGroup 2 T)
    (hTinv : ∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T)
    (hTmax : ∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T)
    {W : Subgroup (psimpleOf p H)} (hW2 : IsPGroup 2 W) (hWinv : ∀ g : 𝔅, ∀ w ∈ W, ψS g w ∈ W)
    (hTW : (T.map (QuotientGroup.mk' (GLAPPrimeCore p H))).map
      (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) ≤ W) :
    W = (T.map (QuotientGroup.mk' (GLAPPrimeCore p H))).map
      (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center (ppQuot p H) with hZ
  set ρ : ppQuot p H →* psimpleOf p H := QuotientGroup.mk' Z with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective Z
  set Tq : Subgroup (ppQuot p H) := T.map (QuotientGroup.mk' (GLAPPrimeCore p H)) with hTq
  have hTq2 : IsPGroup 2 Tq := hT2.map _
  have hρψ : ∀ (g : 𝔅) (x : ppQuot p H), ρ (ψQ g x) = ψS g (ρ x) := fun g x => by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hψS]
  set V := W.comap ρ with hV
  have hVinv : ∀ g : 𝔅, ∀ v ∈ V, ψQ g v ∈ V := by
    intro g v hv
    show ρ (ψQ g v) ∈ W
    rw [hρψ]
    exact hWinv g _ hv
  have hVmap : V.map ρ = W := Subgroup.map_comap_eq_self_of_surjective hρs W
  have hTqV : Tq ≤ V := fun x hx => hTW ⟨x, hx, rfl⟩
  set Nz : Subgroup ↥V := Z.subgroupOf V with hNz
  have hNc : Nz ≤ Subgroup.center ↥V := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hn) (g : ppQuot p H))
  set φV : ↥V →* ↥W := (ρ.comp V.subtype).codRestrict W (fun v => v.2) with hφV
  have hφVs : Function.Surjective φV := by
    intro w
    have hw : (w : psimpleOf p H) ∈ V.map ρ := by rw [hVmap]; exact w.2
    obtain ⟨v, hv, hvw⟩ := hw
    exact ⟨⟨v, hv⟩, Subtype.ext hvw⟩
  have htopW : ∀ P₀ : Sylow 2 ↥V, ((P₀.mapSurjective hφVs : Sylow 2 ↥W) : Subgroup ↥W) = ⊤ := fun P₀ =>
    ((P₀.mapSurjective hφVs).3 (IsPGroup.of_equiv hW2 Subgroup.topEquiv.symm) le_top).symm
  have hsub : Subsingleton (Sylow 2 ↥V) := by
    refine t2021TD4_subsingleton_sylow hNc fun P₀ g => ?_
    have hg : φV g ∈ ((P₀.mapSurjective hφVs : Sylow 2 ↥W) : Subgroup ↥W) := by
      rw [htopW]; trivial
    rw [Sylow.coe_mapSurjective] at hg
    obtain ⟨x, hx, hxg⟩ := hg
    refine ⟨x, hx, ?_⟩
    rw [hNz, Subgroup.mem_subgroupOf]
    have h1 : ρ (x : ppQuot p H) = ρ (g : ppQuot p H) := congrArg Subtype.val hxg
    have h2 := QuotientGroup.eq.1 h1
    simpa using h2
  obtain ⟨P₂⟩ : Nonempty (Sylow 2 ↥V) := inferInstance
  haveI := hsub
  have hchar : (P₂ : Subgroup ↥V).Characteristic := Sylow.characteristic_of_subsingleton P₂
  set V₂ := (P₂ : Subgroup ↥V).map V.subtype with hV₂
  have hTqV₂ : Tq ≤ V₂ := by
    obtain ⟨P₃, hP₃⟩ := (hTq2.comap_of_injective V.subtype V.subtype_injective).exists_le_sylow
    have h3 : P₃ = P₂ := Subsingleton.elim _ _
    intro x hx
    have hx' : (⟨x, hTqV hx⟩ : ↥V) ∈ Tq.comap V.subtype := hx
    exact ⟨⟨x, hTqV hx⟩, h3 ▸ hP₃ hx', rfl⟩
  have hV₂inv : ∀ g : 𝔅, ∀ u ∈ V₂, ψQ g u ∈ V₂ := by
    intro g u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hVeq : V.map (ψQ g).toMonoidHom = V := t2021Fix_map_eq (ψQ g) (hVinv g)
    let eV : ↥V ≃* ↥V := ((ψQ g).subgroupMap V).trans (MulEquiv.subgroupCongr hVeq)
    have heV : ∀ w : ↥V, ((eV w : ↥V) : ppQuot p H) = ψQ g (w : ppQuot p H) := fun w => rfl
    have hfix := (Subgroup.characteristic_iff_map_eq.1 hchar) eV
    have hmem : eV v ∈ (P₂ : Subgroup ↥V) := by
      rw [← hfix]
      exact ⟨v, hv, rfl⟩
    exact ⟨eV v, hmem, heV v⟩
  have hV₂2 : IsPGroup 2 V₂ := P₂.isPGroup'.map V.subtype
  have hV₂eq : V₂ = Tq := t2021Fix_maxQ hp hp2 ψ ψQ hψQ h𝔅 hT2 hTinv hTmax hV₂2 hV₂inv hTqV₂
  refine le_antisymm ?_ hTW
  intro w hw
  have hw' : (⟨w, hw⟩ : ↥W) ∈ ((P₂.mapSurjective hφVs : Sylow 2 ↥W) : Subgroup ↥W) := by
    rw [htopW]; trivial
  rw [Sylow.coe_mapSurjective] at hw'
  obtain ⟨x, hx, hxw⟩ := hw'
  have hxV₂ : (x : ppQuot p H) ∈ Tq := hV₂eq ▸ ⟨x, hx, rfl⟩
  exact ⟨x, hxV₂, congrArg Subtype.val hxw⟩

theorem t2021Fix_radical {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {𝔅 : Type} [Group 𝔅] (ψ : 𝔅 →* MulAut H)
    (ψQ : 𝔅 → MulAut (ppQuot p H))
    (hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l))
    (ψS : 𝔅 → MulAut (psimpleOf p H))
    (hψS : ∀ (g : 𝔅) (x : ppQuot p H), ψS g (QuotientGroup.mk x) = QuotientGroup.mk (ψQ g x))
    (h𝔅 : IsPGroup p 𝔅) {T : Subgroup H} (hT2 : IsPGroup 2 T)
    (hTinv : ∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T)
    (hTmax : ∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer
      (((T.map (QuotientGroup.mk' (GLAPPrimeCore p H))).map
        (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) : Subgroup (psimpleOf p H)) : Set (psimpleOf p H))) =
      (T.map (QuotientGroup.mk' (GLAPPrimeCore p H))).map
        (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Tb : Subgroup (psimpleOf p H) := (T.map (QuotientGroup.mk' (GLAPPrimeCore p H))).map
    (QuotientGroup.mk' (Subgroup.center (ppQuot p H))) with hTb
  have hTb2 : IsPGroup 2 Tb := (hT2.map _).map _
  have hTbinv : ∀ g : 𝔅, ∀ t ∈ Tb, ψS g t ∈ Tb := by
    rintro g _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨_, ⟨ψ g t, hTinv g t ht, rfl⟩, ?_⟩
    simp only [QuotientGroup.mk'_apply]
    rw [hψS, hψQ]
  set W := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Tb : Set (psimpleOf p H))) with hW
  have hTbW : Tb ≤ W :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hTb2
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hWinv : ∀ g : 𝔅, ∀ w ∈ W, ψS g w ∈ W := by
    intro g w hw
    have hNinv : ∀ x ∈ Subgroup.normalizer (Tb : Set (psimpleOf p H)),
        ψS g x ∈ Subgroup.normalizer (Tb : Set (psimpleOf p H)) :=
      fun x hx => t2021Fix_normalizer_inv (ψS g) (hTbinv g) hx
    have hNmap : (Subgroup.normalizer (Tb : Set (psimpleOf p H))).map (ψS g).toMonoidHom =
        Subgroup.normalizer (Tb : Set (psimpleOf p H)) := t2021Fix_map_eq (ψS g) hNinv
    have hle : W.map (ψS g).toMonoidHom ≤ W := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ (hW2.map _)
      · rw [← hNmap]
        exact Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      · rw [← hNmap]
        refine (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)).trans ?_
        exact Subgroup.le_normalizer_map _
    exact hle ⟨w, hw, rfl⟩
  exact (t2021Fix_maxS hp hp2 ψ ψQ hψQ ψS hψS h𝔅 hT2 hTinv hTmax hW2 hWinv hTbW)

theorem t2021Fix_trivAut {p : ℕ} (hperf : commutator (ppQuot p H) = ⊤) (φ : MulAut H)
    (φQ : MulAut (ppQuot p H)) (hφQ : ∀ l : H, φQ (QuotientGroup.mk l) = QuotientGroup.mk (φ l))
    (h1 : MulAut.mapQuotient (Subgroup.center (ppQuot p H)) φQ = 1) : TrivAut p H φ := by
  have hφQ1 : φQ = 1 := eq_one_of_mapQuotient_center_eq_one hperf φQ h1
  intro y
  have h := hφQ y
  rw [hφQ1, MulAut.one_apply] at h
  have h2 := QuotientGroup.eq_iff_div_mem.1 h.symm
  rwa [div_eq_mul_inv] at h2

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
