module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Rho3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Rho2

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup Equiv

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {W X : Type} [Group W]
  [Group X] [Finite W]

omit [Finite G] in
theorem mem_of_central_two {C S : Subgroup G} (hSC : S ≤ C) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex C) {t : G} (htC : t ∈ C) (ht2 : t * t = 1)
    (hcen : ∀ c ∈ C, c * t = t * c) : t ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : ↥C := ⟨t, htC⟩ with htCdef
  have htsq : tC * tC = 1 := Subtype.ext ht2
  have hnorm : (zpowers tC).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : g * tC = tC * g := Subtype.ext (by simpa using hcen g.1 g.2)
    have : g * tC ^ k * g⁻¹ = tC ^ k := by
      rw [(Commute.zpow_right (show Commute g tC from hc) k).eq]
      simp
    rw [this]
    exact zpow_mem_zpowers _ _
  have hpt : IsPGroup 2 (zpowers tC) := by
    have hdvd : orderOf tC ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact htsq)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · refine IsPGroup.of_card (n := 0) ?_
      rw [Nat.card_zpowers, h]
      simp
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, h]
      simp
  have hSp : IsPGroup 2 (S.subgroupOf C) :=
    IsPGroup.of_equiv hS2 (Subgroup.subgroupOfEquivOfLe hSC).symm
  have hidx : ¬ 2 ∣ (S.subgroupOf C).index := hSidx
  have hle := hpt.le_sylow_of_normal (hSp.toSylow hidx)
  have htm : tC ∈ (hSp.toSylow hidx : Subgroup ↥C) := hle (mem_zpowers tC)
  exact htm

theorem outer_choice_abstract (D : AutModelData L W X)
    (hL : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1) (htL : t ∉ L)
    (hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hidx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) = 2)
    (hW : Nat.card W = 2 * Nat.card X) (hZ : ∀ l ∈ L, (∀ x ∈ L, x * l = l * x) → l = 1)
    (hu : ∃ v ∈ centralizer ({t} : Set G), v ∉ L ⊔ zpowers t ∧ v * v = 1)
    (hdata : ∀ Sw : Subgroup W, IsPGroup 2 Sw → ¬ 2 ∣ Sw.index → ∀ zw : W, orderOf zw = 2 →
      centralizer ((Sw ⊓ D.ι.range : Subgroup W) : Set W) ⊓ D.ι.range = zpowers zw →
      OuterData D.ι.range Sw zw)
    {S : Subgroup G} (hSC : S ≤ centralizer ({t} : Set G)) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) {z n : G} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzc : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z)
    (hn : n ∈ normalizer (S : Set G)) (hnt : n * t * n⁻¹ = z * t) :
    ∃ (v s : G) (ψ : Perm (Fin 8) →* G), v ∈ S ∧ v ∉ L ⊔ zpowers t ∧ v * v = 1 ∧ s ∈ S ∧
      s * v * s⁻¹ = v * z ∧ Function.Injective ψ ∧ ψ.range = centralizer ({v} : Set G) ⊓ L ∧
      ¬ (((alternatingGroup (Fin 8)).map ψ).subgroupOf (centralizer ({v} : Set G))).Normal ∧
      ¬ (((alternatingGroup (Fin 8)).map ψ).subgroupOf (centralizer ({t * v} : Set G))).Normal := by
  classical
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  set N' : Subgroup G := L ⊔ zpowers t with hN'def
  have htC : t ∈ C := mem_centralizer_singleton_iff.2 rfl
  have hLC : L ≤ C := le_centralizer_of_mem_centralizer hL
  have ht1 : t ≠ 1 := fun h => htL (h ▸ L.one_mem)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  set ρ : C →* W := D.rhoC hC with hρdef
  have hρker : ∀ x : C, ρ x = 1 ↔ (x : G) ∈ zpowers t := rhoC_eq_one_iff D hC hker
  have hρmem : ∀ x : C, ρ x ∈ D.ι.range ↔ (x : G) ∈ N' := rhoC_mem_range_iff D hC hL hker
  have hρL : ∀ l : L, ρ ⟨l, hLC l.2⟩ = D.ι (D.θ l) := rhoC_of_mem D hC hL
  have hsurj : Function.Surjective ρ := rhoC_surjective D hL hC hker hidx hW
  have hΦinj : Function.Injective (D.ι.comp D.θ.toMonoidHom) := D.ι_injective.comp D.θ.injective
  have hρinj : ∀ a b : L, ρ ⟨a, hLC a.2⟩ = ρ ⟨b, hLC b.2⟩ → a = b := fun a b h => by
    rw [hρL, hρL] at h
    exact hΦinj h
  have hzp : ∀ a : G, a ∈ zpowers t → a = 1 ∨ a = t := by
    intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 ha
    exact zpow_eq_one_or_self ht2 j
  obtain ⟨htS, hSwp, hSwidx⟩ := sylow_range_rhoC D hL ht2 htL hC hker hidx hW S hSC hS2 hSidx
  set σ : S →* W := ρ.comp (Subgroup.inclusion hSC) with hσdef
  set zw : W := D.ι (D.θ ⟨z, hzL⟩) with hzw
  have hzρ : ρ ⟨z, hLC hzL⟩ = zw := hρL ⟨z, hzL⟩
  have hzw2 : orderOf zw = 2 := by
    have h := orderOf_injective _ hΦinj ⟨z, hzL⟩
    rw [show zw = (D.ι.comp D.θ.toMonoidHom) ⟨z, hzL⟩ from rfl, h, Subgroup.orderOf_mk, hz2]
  have hcent := centralizer_range_rhoS D hL hC hker S hSC htS z hzL hzc
  obtain ⟨yw, sw, ψ, hyS, hyQ, hy2, hsS, hsy, hψ, hrange, ⟨σ₀, hσ₀, hψz⟩, ⟨κ, hκ, hψκ⟩, hF2,
    hgen, hF1⟩ := hdata σ.range hSwp hSwidx zw hzw2 hcent
  obtain ⟨v', hv'⟩ := hyS
  obtain ⟨s', hs'⟩ := hsS
  set v : G := (v' : G) with hvdef
  set s : G := (s' : G) with hsdef
  have hvS : v ∈ S := v'.2
  have hsS' : s ∈ S := s'.2
  have hvC : v ∈ C := hSC hvS
  have hsC : s ∈ C := hSC hsS'
  have hρv : ρ ⟨v, hvC⟩ = yw := hv'
  have hρs : ρ ⟨s, hsC⟩ = sw := hs'
  have hvN : v ∉ N' := fun h => hyQ (hρv ▸ (hρmem ⟨v, hvC⟩).2 h)
  obtain ⟨v₀, hv₀C, hv₀N, hv₀2⟩ := hu
  have hvsq : v * v = 1 :=
    mul_self_eq_one_of_lift D hL ht2 htL hC hker hidx hv₀C hv₀N hv₀2 hvC (by rw [hρv, hy2])
  have hsv : s * v * s⁻¹ = v * z := by
    have h1 : ρ (⟨s, hsC⟩ * ⟨v, hvC⟩ * ⟨s, hsC⟩⁻¹ * (⟨v, hvC⟩ * ⟨z, hLC hzL⟩)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hρs, hρv, hzρ, hsy, mul_inv_cancel]
    have h2 : s * v * s⁻¹ * (v * z)⁻¹ ∈ zpowers t := (hρker _).1 h1
    rcases hzp _ h2 with h | h
    · calc s * v * s⁻¹ = (s * v * s⁻¹ * (v * z)⁻¹) * (v * z) := by group
        _ = v * z := by rw [h, one_mul]
    · exfalso
      have h3 : s * v * s⁻¹ = t * (v * z) := by
        calc s * v * s⁻¹ = (s * v * s⁻¹ * (v * z)⁻¹) * (v * z) := by group
          _ = t * (v * z) := by rw [h]
      have h4 := comm_mem_of_mem_centralizer hL hC hidx hsC hvC
      have h5 : v * z * v⁻¹ ∈ L := (mem_normalizer_iff.1 (hC hvC) z).1 hzL
      apply htL
      have : t = (s * v * s⁻¹ * v⁻¹) * (v * z * v⁻¹)⁻¹ := by
        rw [h3]
        group
      rw [this]
      exact L.mul_mem h4 (L.inv_mem h5)
  have hψQ : ∀ τ, ψ τ ∈ D.ι.range := fun τ =>
    (hrange ▸ ⟨τ, rfl⟩ : ψ τ ∈ centralizer ({yw} : Set W) ⊓ D.ι.range).2
  let Θ : L ≃* ↥D.ι.range := D.θ.trans (MonoidHom.ofInjective D.ι_injective)
  let ψG : Perm (Fin 8) →* G :=
    L.subtype.comp (Θ.symm.toMonoidHom.comp (ψ.codRestrict D.ι.range hψQ))
  have hψGL : ∀ τ, ψG τ ∈ L := fun τ => (Θ.symm ⟨ψ τ, hψQ τ⟩).2
  have hρψG : ∀ τ, ρ ⟨ψG τ, hLC (hψGL τ)⟩ = ψ τ := by
    intro τ
    have h1 := hρL (Θ.symm ⟨ψ τ, hψQ τ⟩)
    have h2 : ((Θ (Θ.symm ⟨ψ τ, hψQ τ⟩) : ↥D.ι.range) : W) = ψ τ := by
      rw [Θ.apply_symm_apply]
    exact h1.trans h2
  have hψGinj : Function.Injective ψG := by
    intro a b h
    apply hψ
    rw [← hρψG a, ← hρψG b]
    exact congrArg ρ (Subtype.ext h)
  have hcommL : ∀ l : L, ρ ⟨l, hLC l.2⟩ * yw = yw * ρ ⟨l, hLC l.2⟩ → (l : G) * v = v * l := by
    intro l hl
    have h1 : ρ (⟨l, hLC l.2⟩ * ⟨v, hvC⟩ * ⟨l, hLC l.2⟩⁻¹ * ⟨v, hvC⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv, hρv]
      rw [hl]
      group
    have h2 : (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ zpowers t := (hρker _).1 h1
    have h3 : (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ L := by
      have h4 : v * (l : G)⁻¹ * v⁻¹ ∈ L := (mem_normalizer_iff.1 (hC hvC) _).1 (L.inv_mem l.2)
      have : (l : G) * v * (l : G)⁻¹ * v⁻¹ = (l : G) * (v * (l : G)⁻¹ * v⁻¹) := by group
      rw [this]
      exact L.mul_mem l.2 h4
    rcases hzp _ h2 with h | h
    · calc (l : G) * v = ((l : G) * v * (l : G)⁻¹ * v⁻¹) * (v * l) := by group
        _ = v * l := by rw [h, one_mul]
    · exact absurd (h ▸ h3) htL
  have hcommL' : ∀ l : L, (l : G) * v = v * l → ρ ⟨l, hLC l.2⟩ * yw = yw * ρ ⟨l, hLC l.2⟩ := by
    intro l hl
    have := congrArg ρ (show (⟨l, hLC l.2⟩ * ⟨v, hvC⟩ : C) = ⟨v, hvC⟩ * ⟨l, hLC l.2⟩ from
      Subtype.ext hl)
    simpa only [map_mul, hρv] using this
  have hrangeG : ψG.range = centralizer ({v} : Set G) ⊓ L := by
    ext l
    constructor
    · rintro ⟨τ, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.2 ?_, hψGL τ⟩
      refine hcommL ⟨ψG τ, hψGL τ⟩ ?_
      rw [hρψG]
      have h1 : ψ τ ∈ centralizer ({yw} : Set W) ⊓ D.ι.range := hrange ▸ ⟨τ, rfl⟩
      exact mem_centralizer_singleton_iff.1 h1.1
    · rintro ⟨h1, hl⟩
      have h2 : l * v = v * l := mem_centralizer_singleton_iff.1 h1
      have h3 := hcommL' ⟨l, hl⟩ h2
      have h4 : ρ ⟨l, hLC hl⟩ ∈ ψ.range := by
        rw [hrange]
        refine ⟨mem_centralizer_singleton_iff.2 h3, ?_⟩
        rw [hρL ⟨l, hl⟩]
        exact ⟨_, rfl⟩
      obtain ⟨τ, hτ⟩ := h4
      refine ⟨τ, ?_⟩
      have := hρinj ⟨ψG τ, hψGL τ⟩ ⟨l, hl⟩ (by rw [hρψG, hτ])
      exact congrArg Subtype.val this
  have hψGz : ψG σ₀ = z := by
    have := hρinj ⟨ψG σ₀, hψGL σ₀⟩ ⟨z, hzL⟩ (by rw [hρψG, hψz, hzρ])
    exact congrArg Subtype.val this
  have hψGκ : ψG κ * z = z * ψG κ := by
    have h1 : ρ (⟨ψG κ, hLC (hψGL κ)⟩ * ⟨z, hLC hzL⟩) =
        ρ (⟨z, hLC hzL⟩ * ⟨ψG κ, hLC (hψGL κ)⟩) := by
      rw [map_mul, map_mul, hρψG, hzρ, hψκ]
    have := hρinj ⟨ψG κ * z, L.mul_mem (hψGL κ) hzL⟩ ⟨z * ψG κ, L.mul_mem hzL (hψGL κ)⟩ h1
    exact congrArg Subtype.val this
  have hΛL : (alternatingGroup (Fin 8)).map ψG ≤ L := by
    rintro _ ⟨a, -, rfl⟩
    exact hψGL a
  have hΛ₂L : ((alternatingGroup (Fin 8)).map ψG).map (MulAut.conj s).toMonoidHom ≤ L := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
    exact (mem_normalizer_iff.1 (hC hsC) _).1 (hψGL a)
  have hgenG : (alternatingGroup (Fin 8)).map ψG ⊔
      ((alternatingGroup (Fin 8)).map ψG).map (MulAut.conj s).toMonoidHom = L := by
    refine le_antisymm (sup_le hΛL hΛ₂L) ?_
    set K : Subgroup G := (alternatingGroup (Fin 8)).map ψG ⊔
      ((alternatingGroup (Fin 8)).map ψG).map (MulAut.conj s).toMonoidHom with hK
    have hKL : K ≤ L := sup_le hΛL hΛ₂L
    set Kc : Subgroup C := K.comap C.subtype with hKc
    have h1 : (alternatingGroup (Fin 8)).map ψ ≤ Kc.map ρ := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨⟨ψG a, hLC (hψGL a)⟩, ?_, hρψG a⟩
      exact le_sup_left (a := (alternatingGroup (Fin 8)).map ψG) ⟨a, ha, rfl⟩
    have h2 : ((alternatingGroup (Fin 8)).map ψ).map (MulAut.conj sw).toMonoidHom ≤
        Kc.map ρ := by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨⟨s, hsC⟩ * ⟨ψG a, hLC (hψGL a)⟩ * ⟨s, hsC⟩⁻¹, ?_, ?_⟩
      · show s * ψG a * s⁻¹ ∈ K
        exact le_sup_right (b := ((alternatingGroup (Fin 8)).map ψG).map
          (MulAut.conj s).toMonoidHom) ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      · simp only [map_mul, map_inv, hρs, hρψG]
        rfl
    have h3 : D.ι.range ≤ Kc.map ρ := hgen.trans (sup_le h1 h2)
    intro l hl
    have h4 : ρ ⟨l, hLC hl⟩ ∈ D.ι.range := by
      rw [hρL ⟨l, hl⟩]
      exact ⟨_, rfl⟩
    obtain ⟨k, hk, hkl⟩ := h3 h4
    have hkL : (k : G) ∈ L := hKL hk
    have := hρinj ⟨k, hkL⟩ ⟨l, hl⟩ hkl
    have h5 : (k : G) = l := congrArg Subtype.val this
    rw [← h5]
    exact hk
  have hNC : ∀ h ∈ normalizer (L : Set G), ∃ c ∈ centralizer ({t} : Set G),
      h * c⁻¹ ∈ centralizer (L : Set G) := by
    intro h hh
    obtain ⟨c, hc⟩ := hsurj (D.rho ⟨h, hh⟩)
    refine ⟨c, c.2, ?_⟩
    have h1 : D.rho (⟨h, hh⟩ * ⟨c, hC c.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv]
      have : D.rho ⟨c, hC c.2⟩ = ρ c := rfl
      rw [this, hc, mul_inv_cancel]
    exact (D.rho_eq_one_iff _).1 h1
  have hno5 : ∀ u ∈ centralizer ({t} : Set G), u * v = v * u → u * z = z * u → u ^ 5 = 1 →
      u = 1 := by
    intro u hu huv huz hu5
    have huN' : u ∈ N' := mem_sup_of_pow_odd hidx hu (m := 2) hu5
    have hρuQ : ρ ⟨u, hu⟩ ∈ D.ι.range := (hρmem ⟨u, hu⟩).2 huN'
    have hρuy : ρ ⟨u, hu⟩ * yw = yw * ρ ⟨u, hu⟩ := by
      have := congrArg ρ (show (⟨u, hu⟩ * ⟨v, hvC⟩ : C) = ⟨v, hvC⟩ * ⟨u, hu⟩ from Subtype.ext huv)
      simpa only [map_mul, hρv] using this
    have hρuz : ρ ⟨u, hu⟩ * zw = zw * ρ ⟨u, hu⟩ := by
      have := congrArg ρ (show (⟨u, hu⟩ * ⟨z, hLC hzL⟩ : C) = ⟨z, hLC hzL⟩ * ⟨u, hu⟩ from
        Subtype.ext huz)
      simpa only [map_mul, hzρ] using this
    have hρu5 : ρ ⟨u, hu⟩ ^ 5 = 1 := by
      rw [← map_pow]
      have : (⟨u, hu⟩ : C) ^ 5 = 1 := Subtype.ext hu5
      rw [this, map_one]
    have h1 : ρ ⟨u, hu⟩ ∈ ψ.range := by
      rw [hrange]
      exact ⟨mem_centralizer_singleton_iff.2 hρuy, hρuQ⟩
    obtain ⟨τ, hτ⟩ := h1
    have h2 : ψ τ = 1 := hF2 τ (by rw [hτ]; exact hρuz) (by rw [hτ]; exact hρu5)
    rw [hτ] at h2
    rcases hzp u ((hρker ⟨u, hu⟩).1 h2) with h | h
    · exact h
    · exfalso
      rw [h] at hu5
      apply ht1
      calc t = (t * t) * (t * t) * t := by rw [ht2, one_mul, one_mul]
        _ = t ^ 5 := by simp [pow_succ, mul_assoc]
        _ = 1 := hu5
  have hfive : ∀ x ∈ S, x * x = 1 → x ≠ 1 → x ≠ t →
      ∃ u ∈ centralizer ({t} : Set G), u ^ 5 = 1 ∧ u ≠ 1 ∧ u * x = x * u := by
    intro x hxS hx2 hx1 hxt
    have hxC : x ∈ C := hSC hxS
    have hρxS : ρ ⟨x, hxC⟩ ∈ σ.range := ⟨⟨x, hxS⟩, rfl⟩
    have hρx2 : ρ ⟨x, hxC⟩ * ρ ⟨x, hxC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hxC⟩ * ⟨x, hxC⟩ : C) = 1 := Subtype.ext hx2
      rw [this, map_one]
    have hρx1 : ρ ⟨x, hxC⟩ ≠ 1 := by
      intro h
      rcases hzp x ((hρker ⟨x, hxC⟩).1 h) with h' | h'
      · exact hx1 h'
      · exact hxt h'
    obtain ⟨r, hr5, hr1, hrc⟩ := hF1 _ hρxS hρx2 hρx1
    obtain ⟨u, huC, hρu, hu5⟩ := exists_lift_pow_five D ht2 hC hker hsurj hr5
    refine ⟨u, huC, hu5, ?_, ?_⟩
    · intro h
      subst h
      apply hr1
      have h1 : (⟨1, huC⟩ : C) = 1 := rfl
      rw [h1, map_one] at hρu
      exact hρu.symm
    · exact commute_of_pow_odd D ht2 ht1 hC hker huC hxC (m := 2) hu5 (by
        rw [hρu]
        exact hrc)
  have htS : t ∈ S :=
    mem_of_central_two hSC hS2 hSidx htC ht2 (fun c hc => mem_centralizer_singleton_iff.1 hc)
  exact ⟨v, s, ψG, hvS, hvN, hvsq, hsS', hsv, hψGinj, hrangeG,
    not_normal_of_data hL hC hZ hNC hzL hn hnt hvS hvsq hvN hsv ψG hψGinj hrangeG hσ₀ hψGz hκ
      hψGκ hgenG hno5 hfive,
    not_normal_mul_of_data hL hC hZ hNC hzL hn hnt hSC htS ht2 hvS hvsq hvN hsS' hsv ψG hψGinj
      hrangeG hσ₀ hψGz hκ hψGκ hgenG hno5 hfive⟩

end CFSG.EvenSporadicStandard.HSStd
