module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415W0
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem pPrimeCore_eq_bot_of_simple_even {Y : Type*} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hev : 2 ∣ Nat.card Y) : pPrimeCore 2 Y = ⊥ := by
  have : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ this with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcop := pPrimeCore_coprime_card (p := 2) (G := Y)
    rw [h, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop hev

theorem exists_lift_two_component' {X : Type} [Group X] [Finite X] {β z : X}
    (hzβ : z ∈ centralizer ({β} : Set X)) (hz : orderOf z = 2) {Y : Subgroup (MBar β)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)})
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)}))) :
    ∃ J : Subgroup X, J ≤ centralizer {β} ⊓ centralizer {z} ∧
      IsPComponent 2 (J.subgroupOf (centralizer {β} ⊓ centralizer {z})) ∧
      (∀ x (hx : x ∈ centralizer ({β} : Set X)), x ∈ centralizer ({z} : Set X) →
        (∃ k : ℕ, orderOf x = 2 ^ k) → (QuotientGroup.mk ⟨x, hx⟩ : MBar β) ∈ Y → x ∈ J) ∧
      (J.subgroupOf (centralizer {β})).map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
        ({β} : Set X)))) = Y ∧
      ∃ g : ↥J →* ↥Y, Function.Surjective g ∧ ¬ 2 ∣ Nat.card g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({β} : Set X)
  let z' : ↥M := ⟨z, hzβ⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({z'} : Set ↥M)
  have hz'2 : z' * z' = 1 := Subtype.ext (by
    change z * z = 1
    rw [← sq, ← hz, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :=
    map_centralizer_eq hodd hz'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} : Set (MBar β))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨-, hlift, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  obtain ⟨hĴ, hĴmap⟩ := hlift _ hY
  have hCX : C.map M.subtype = centralizer {β} ⊓ centralizer {z} := by
    rw [map_subtype_centralizer hzβ, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({β} : Set X) ⊓ centralizer {z}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  generalize hĴdef : closure {x : ↥C | x ∈ (Y.subgroupOf (centralizer
    {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)})).comap φ ∧ ∃ k : ℕ, orderOf x = 2 ^ k} = Ĵ at hĴ hĴmap
  have hJle : (Ĵ.map C.subtype).map M.subtype ≤ centralizer {β} ⊓ centralizer {z} := by
    rw [← hCX]
    exact map_mono (map_subtype_le Ĵ)
  have hJeq : ((Ĵ.map C.subtype).map M.subtype).subgroupOf (centralizer {β} ⊓ centralizer {z}) =
      Ĵ.map eC.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : ((eC y : ↥(centralizer ({β} : Set X) ⊓ centralizer {z})) : X) = x :=
        congrArg Subtype.val hyx
      exact ⟨(y : ↥M), ⟨y, hy, rfl⟩, h1⟩
  refine ⟨(Ĵ.map C.subtype).map M.subtype, hJle,
    by rw [hJeq]; exact isPComponent_map_mulEquiv eC hĴ, ?_, ?_, ?_⟩
  ·
    intro x hx hxz ⟨k, hk⟩ hxY
    have hxC : (⟨x, hx⟩ : ↥M) ∈ C := by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxz)
    have hxĴ : (⟨⟨x, hx⟩, hxC⟩ : ↥C) ∈ Ĵ := by
      rw [← hĴdef]
      refine subset_closure ⟨hxY, k, ?_⟩
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact hk
    exact ⟨_, ⟨_, hxĴ, rfl⟩, rfl⟩
  ·
    have h1 : ((Ĵ.map C.subtype).map M.subtype).subgroupOf M = Ĵ.map C.subtype :=
      comap_map_eq_self_of_injective M.subtype_injective _
    have hcomp : π.comp C.subtype = (centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
        Set (MBar β))).subtype.comp φ := rfl
    rw [h1, map_map, hcomp, ← map_map, hĴmap, subgroupOf_map_subtype, inf_eq_left.mpr hYle]
  ·
    let eJ : ↥Ĵ ≃* ↥((Ĵ.map C.subtype).map M.subtype) :=
      ((Ĵ.equivMapOfInjective C.subtype C.subtype_injective).trans
        ((Ĵ.map C.subtype).equivMapOfInjective M.subtype M.subtype_injective))
    have hφĴ : ∀ x : ↥Ĵ, ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
        Set (MBar β)))) : MBar β) ∈ Y := by
      intro x
      have : φ x ∈ Ĵ.map φ := mem_map_of_mem φ x.2
      rw [hĴmap] at this
      exact this
    let g₀ : ↥Ĵ →* ↥Y := ((centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
      Set (MBar β))).subtype.comp (φ.comp Ĵ.subtype)).codRestrict Y hφĴ
    have hg₀ : Function.Surjective g₀ := by
      rintro ⟨y, hy⟩
      have hy' : (⟨y, hYle hy⟩ : ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :
          Set (MBar β)))) ∈ Ĵ.map φ := by
        rw [hĴmap]; exact hy
      obtain ⟨x, hx, hxy⟩ := hy'
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      show ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} : Set (MBar β)))) :
        MBar β) = y
      rw [hxy]
    have hg₀k : ¬ 2 ∣ Nat.card g₀.ker := by
      have hle : g₀.ker.map Ĵ.subtype ≤ φ.ker := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : g₀ x = 1 := hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have h2 := congrArg Subtype.val hx'
        exact h2
      have hc : Nat.card g₀.ker ∣ Nat.card φ.ker := by
        rw [← Subgroup.card_map_of_injective Ĵ.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      exact fun h2 => hφk (h2.trans hc)
    refine ⟨g₀.comp eJ.symm.toMonoidHom, hg₀.comp eJ.symm.surjective, ?_⟩
    have hk : Nat.card (g₀.comp eJ.symm.toMonoidHom).ker = Nat.card g₀.ker := by
      rw [← MonoidHom.comap_ker]
      exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ eJ.symm.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [Subgroup.map_comap_eq_self_of_surjective eJ.symm.surjective]))).toEquiv
    rw [hk]
    exact hg₀k

theorem exists_K₂_of {X : Type} [Group X] [Finite X] {β t z₁ : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X))
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W) (hz₁W : z₁ ∈ W)
    (hz₁2 : z₁ ^ 2 = 1) (hz₁ne : z₁ ≠ t * z₁ * t⁻¹)
    (hmk : ∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
      (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁)
    (hz₁₂ : z₁ * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * z₁) (ht2 : t * t = 1) :
    ∃ K₂ : Subgroup X, IsTwoComponentIn K₂ (centralizer {z₁} ⊓ centralizer {β}) ∧
      Nonempty (↥K₂ ⧸ pPrimeCore 2 ↥K₂ ≃* ↥Kb₁) ∧ t * z₁ * t⁻¹ ∈ K₂ ∧
      (K₂.subgroupOf (centralizer {β})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))) = Kb₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  have hWM : W ≤ M := hW.le
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hz₁M : z₁ ∈ M := hWM hz₁W
  have hz₁o : orderOf z₁ = 2 := orderOf_eq_prime hz₁2 (fun h1 => hz₁ne (by
    rw [h1]; group))
  set zb₁ : MBar β := QuotientGroup.mk ⟨z₁, hz₁M⟩ with hzb₁
  have hzbK : zb₁ ∈ Kb₁ := hmk hz₁M
  have hK₂c : Kb₂ ≤ centralizer {zb₁} := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hprod.comm hzbK hk).symm
  have hK₂n : ∀ g ∈ centralizer ({zb₁} : Set (MBar β)), ∀ k ∈ Kb₂, g * k * g⁻¹ ∈ Kb₂ := by
    intro g hg k hk
    rcases hprod.conj_cases hE g with h1 | h1
    ·
      have hK₂ : Kb₂.map (MulAut.conj g).toMonoidHom = Kb₂ := by
        rcases LocalCores.distinct_components_commute
            (LocalCores.isComponent_map_mulEquiv (MulAut.conj g) (hprod.isComponent₂ hE))
            (hprod.isComponent₂ hE) with h2 | h2
        · exact h2
        · exfalso
          rcases LocalCores.distinct_components_commute
              (LocalCores.isComponent_map_mulEquiv (MulAut.conj g) (hprod.isComponent₂ hE))
              (hprod.isComponent₁ hE) with h3 | h3
          · apply hprod.K₁_ne_K₂
            apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
              (MulAut.conj g).injective
            rw [h1, h3]
          · have hNE : Kb₂.map (MulAut.conj g).toMonoidHom ≤ layer (MBar β) := by
              rintro _ ⟨y, hy, rfl⟩
              exact hE.conj_mem y (hprod.K₂_le hy) g
            have hb := hprod.eq_bot_of_commute hNE h3 h2
            obtain ⟨a, b, hab⟩ := hprod.nonabelian₂
            apply hab
            have ha : (MulAut.conj g) (a : MBar β) ∈ (⊥ : Subgroup (MBar β)) :=
              hb ▸ ⟨a, a.2, rfl⟩
            have hb' : (MulAut.conj g) (b : MBar β) ∈ (⊥ : Subgroup (MBar β)) :=
              hb ▸ ⟨b, b.2, rfl⟩
            rw [mem_bot, map_eq_one_iff _ (MulAut.conj g).injective] at ha hb'
            exact Subtype.ext (by simp [ha, hb'])
      rw [← hK₂]
      exact ⟨k, hk, rfl⟩
    ·
      exfalso
      have h2 : g * zb₁ * g⁻¹ ∈ Kb₂ := by
        rw [← h1]
        exact ⟨zb₁, hzbK, rfl⟩
      have h3 : g * zb₁ * g⁻¹ = zb₁ := by
        rw [mem_centralizer_singleton_iff.mp hg]
        group
      have h4 : zb₁ ∈ Kb₁ ⊓ Kb₂ := mem_inf.mpr ⟨hzbK, h3 ▸ h2⟩
      rw [hprod.inf_eq, mem_bot] at h4
      have h5 : z₁ = 1 := mk_injOn hWM hW.isPGroup hz₁W (one_mem W)
        (h4.trans rfl)
      exact hz₁ne (by rw [h5]; group)
  have hsimp := hprod.simple₂
  have hnab := hprod.nonabelian₂
  have hq : IsQuasisimple ↥Kb₂ := HarrisEnd.isQuasisimple_of_isSimpleGroup hnab
  have hz₂M : t * z₁ * t⁻¹ ∈ M := mul_mem (mul_mem htM hz₁M) (inv_mem htM)
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem htW hz₁W) (inv_mem htW)
  have hzb₂ : (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hz₂M⟩ : MBar β) ∈ Kb₂ := by
    have h := hprod.conj_mem_K₂ hzbK
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    convert h using 1
    rw [hzb₁, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show t * z₁ * t⁻¹ = t⁻¹ * z₁ * t
    rw [hti]
  have hz₂2 : (t * z₁ * t⁻¹) ^ 2 = 1 := by
    rw [sq, show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ by group, ← sq, hz₁2]
    group
  have hz₂1 : t * z₁ * t⁻¹ ≠ 1 := fun h1 => hz₁ne (by
    have : z₁ = 1 := by
      calc z₁ = t⁻¹ * (t * z₁ * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    rw [this]; group)
  have hzb₂o : orderOf (QuotientGroup.mk ⟨t * z₁ * t⁻¹, hz₂M⟩ : MBar β) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hz₂1 ?_
    · rw [← QuotientGroup.mk_pow]
      have : (⟨t * z₁ * t⁻¹, hz₂M⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]; exact hz₂2)
      rw [this, QuotientGroup.mk_one]
    · exact mk_injOn hWM hW.isPGroup hz₂W (one_mem W) (h1.trans rfl)
  have hev : 2 ∣ Nat.card ↥Kb₂ := by
    have h1 := orderOf_dvd_natCard (⟨_, hzb₂⟩ : ↥Kb₂)
    rwa [Subgroup.orderOf_mk, hzb₂o] at h1
  have hO : pPrimeCore 2 ↥Kb₂ = ⊥ := L415.pPrimeCore_eq_bot_of_simple_even hsimp hev
  have hq2 : IsTwoQuasisimple ↥Kb₂ :=
    ⟨hq.1, HarrisEnd.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩
  have hnorm : (Kb₂.subgroupOf (centralizer {zb₁})).Normal :=
    ⟨fun a ha g => hK₂n g g.2 a ha⟩
  have hTC : IsTwoComponentIn Kb₂ (centralizer {zb₁}) := ⟨hK₂c, hnorm.isSubnormal, hq2⟩
  have hPC := (isTwoComponentIn_iff hK₂c).mp hTC
  obtain ⟨J, hJle, hJp, hJmem, hJmap, g, hg, hgk⟩ :=
    L415.exists_lift_two_component' hz₁M hz₁o hK₂c hPC
  have hJ : IsTwoComponentIn J (centralizer {β} ⊓ centralizer {z₁}) :=
    (isTwoComponentIn_iff hJle).mpr hJp
  rw [inf_comm] at hJ
  obtain ⟨eO⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hg hgk
  refine ⟨J, hJ, ⟨eO.trans (((QuotientGroup.quotientMulEquivOfEq hO).trans
    QuotientGroup.quotientBot).trans hprod.equivK₂.symm)⟩, ?_, hJmap⟩
  refine hJmem _ hz₂M ?_ ⟨1, by rw [pow_one]; exact orderOf_eq_prime hz₂2 hz₂1⟩ hzb₂
  exact mem_centralizer_singleton_iff.mpr hz₁₂.symm


end L415


variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem z₁_comm_z₂ : z₁ * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * z₁ :=
  mem_centralizer_singleton_iff.mp (hc.W₀_le_z₂ (mem_inf.mpr ⟨hc.z₁_mem,
    mem_centralizer_singleton_iff.mpr rfl⟩))

theorem exists_K₂ :
    ∃ K₂ : Subgroup X, IsTwoComponentIn K₂
        (centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      Nonempty (↥K₂ ⧸ pPrimeCore 2 ↥K₂ ≃*
        ↥(Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      t * z₁ * t⁻¹ ∈ K₂ ∧
      (K₂.subgroupOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
          ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) = Kb₂ := by
  obtain ⟨K₂, h1, ⟨e⟩, h3, h4⟩ := L415.exists_K₂_of (hc.isSylowOf_W.le hc.t_mem_W) hc.prod
    hc.isSylowOf_W hc.t_mem_W hc.z₁_mem hc.sq_z₁ hc.z₁_ne hc.mk_z₁ hc.z₁_comm_z₂
    (by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one])
  obtain ⟨e₁⟩ := hc.equiv₁
  exact ⟨K₂, h1, ⟨e.trans e₁⟩, h3, h4⟩

end Config415

end CFSG.ComponentClassification.HarrisLit
