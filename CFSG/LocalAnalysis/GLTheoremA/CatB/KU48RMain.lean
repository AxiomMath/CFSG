module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KU48RCount
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Core

public section

noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 σ4 exists_conj_field4 fieldFactor4)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48.X8 (Rs Xs act dotB Rs_ne_bot)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {G : Type} [Group G]

@[expose] def conjL (L : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha x).1 x.2⟩
  invFun x := ⟨a⁻¹ * x * a, (Subgroup.mem_normalizer_iff.1 ha (a⁻¹ * x * a)).2
    (by simpa [mul_assoc] using x.2)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjL_val (L : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    ((conjL L a ha x : ↥L) : G) = a * (x : G) * a⁻¹ :=
  rfl

theorem conjL_mul (L : Subgroup G) (a b : G) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hab : a * b ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : conjL L (a * b) hab x = conjL L a ha (conjL L b hb x) :=
  Subtype.ext (by simp [conjL_val, mul_assoc])

theorem conjL_one (L : Subgroup G) (h : (1 : G) ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    conjL L 1 h x = x :=
  Subtype.ext (by simp [conjL_val])

@[expose] def alphaA {L : Subgroup G} (e : ↥L ≃* SU4) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    MulAut SU4 :=
  (e.symm.trans (conjL L a ha)).trans e

theorem alphaA_apply {L : Subgroup G} (e : ↥L ≃* SU4) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : alphaA e a ha (e x) = e (conjL L a ha x) := by
  simp [alphaA]

theorem alphaA_mul {L : Subgroup G} (e : ↥L ≃* SU4) (a b : G) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hab : a * b ∈ Subgroup.normalizer (L : Set G)) :
    (alphaA e (a * b) hab).toMonoidHom = (alphaA e a ha).toMonoidHom.comp (alphaA e b hb).toMonoidHom := by
  apply MonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  change alphaA e (a * b) hab (e x) = alphaA e a ha (alphaA e b hb (e x))
  simp only [alphaA_apply]
  rw [conjL_mul L a b ha hb hab]

theorem alphaA_one {L : Subgroup G} (e : ↥L ≃* SU4) (h : (1 : G) ∈ Subgroup.normalizer (L : Set G)) :
    (alphaA e 1 h).toMonoidHom = MonoidHom.id SU4 := by
  apply MonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  change alphaA e 1 h (e x) = e x
  rw [alphaA_apply, conjL_one]


theorem alphaA_toMonoidHom_congr {L : Subgroup G} (e : ↥L ≃* SU4) {a a' : G} (h : a = a')
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha' : a' ∈ Subgroup.normalizer (L : Set G)) :
    (alphaA e a ha).toMonoidHom = (alphaA e a' ha').toMonoidHom := by
  subst h
  rfl

theorem symm_alphaA {L : Subgroup G} (e : ↥L ≃* SU4) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (s : SU4) : (((e.symm (alphaA e a ha s)) : ↥L) : G) = a * ((e.symm s : ↥L) : G) * a⁻¹ := by
  obtain ⟨x, rfl⟩ := e.surjective s
  rw [alphaA_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, conjL_val]

@[expose] def TT {L T : Subgroup G} (e : ↥L ≃* SU4) : Subgroup SU4 :=
  (T.subgroupOf L).map (e.toMonoidHom)

theorem TT_invariant {L T : Subgroup G} (e : ↥L ≃* SU4) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (haT : a ∈ Subgroup.normalizer (T : Set G)) :
    (∀ s ∈ TT (T := T) e, alphaA e a ha s ∈ TT (T := T) e) ∧
      (∀ s ∈ TT (T := T) e, (alphaA e a ha).symm s ∈ TT (T := T) e) := by
  have key : ∀ s : SU4, s ∈ TT (T := T) e ↔ ((e.symm s : ↥L) : G) ∈ T := by
    intro s
    unfold TT
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxs⟩
      have : e.symm s = x := by rw [← hxs]; exact e.symm_apply_apply x
      rw [this]
      exact Subgroup.mem_subgroupOf.1 hx
    · intro h
      exact ⟨e.symm s, Subgroup.mem_subgroupOf.2 h, by simp⟩
  constructor
  · intro s hs
    rw [key] at hs ⊢
    rw [symm_alphaA]
    exact (Subgroup.mem_normalizer_iff.1 haT _).1 hs
  · intro s hs
    rw [key] at hs ⊢
    set u := (alphaA e a ha).symm s with hu
    have hus : alphaA e a ha u = s := (alphaA e a ha).apply_symm_apply s
    have hsymm := symm_alphaA e a ha u
    rw [hus] at hsymm
    apply (Subgroup.mem_normalizer_iff.1 haT _).2
    rw [← hsymm]
    exact hs

@[expose] def Wof (TT : Subgroup SU4) : Subgroup (GL (Fin 4) KF) :=
  TT.map (CFSG.LieType.Universal.Unitary.SUid σ4 4).subtype

theorem mem_Wof {TT : Subgroup SU4} {t : GL (Fin 4) KF} :
    t ∈ Wof TT ↔ ∃ s ∈ TT, (s : GL (Fin 4) KF) = t := by
  unfold Wof
  rw [Subgroup.mem_map]
  rfl

theorem Wof_unitary (TT : Subgroup SU4) :
    ∀ w ∈ Wof TT, (((w : Matrix (Fin 4) (Fin 4) KF).map hKF.bar))ᵀ * (w : Matrix (Fin 4) (Fin 4) KF) = 1 := by
  intro w hw
  obtain ⟨s, -, rfl⟩ := mem_Wof.1 hw
  exact SU4_unitary s

theorem Wof_perm (TT : Subgroup SU4) (α : MulAut SU4) (g : SU4) (φ : KF ≃+* KF)
    (hα : ∀ x : SU4, ((α x : SU4) : GL (Fin 4) KF) =
      (g : GL (Fin 4) KF) * glAut φ (x : GL (Fin 4) KF) * (g : GL (Fin 4) KF)⁻¹)
    (h1 : ∀ s ∈ TT, α s ∈ TT) (h2 : ∀ s ∈ TT, α.symm s ∈ TT) :
    (∀ t ∈ Wof TT, ∃ t' ∈ Wof TT, (g : GL (Fin 4) KF) * glAut φ t' * (g : GL (Fin 4) KF)⁻¹ = t) ∧
      (∀ t ∈ Wof TT, (g : GL (Fin 4) KF) * glAut φ t * (g : GL (Fin 4) KF)⁻¹ ∈ Wof TT) := by
  constructor
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_Wof.1 ht
    refine ⟨((α.symm s : SU4) : GL (Fin 4) KF), mem_Wof.2 ⟨α.symm s, h2 s hs, rfl⟩, ?_⟩
    rw [← hα (α.symm s), MulEquiv.apply_symm_apply]
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_Wof.1 ht
    exact mem_Wof.2 ⟨α s, h1 s hs, hα s⟩

theorem om_alphaA {L T : Subgroup G} (e : ↥L ≃* SU4) (a : G) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (haT : a ∈ Subgroup.normalizer (T : Set G)) {X : Subgroup SU4} (hX : X ∈ Om (Rs (Wof (TT (T := T) e)))) :
    X.map (alphaA e a ha).toMonoidHom ∈ Om (Rs (Wof (TT (T := T) e))) := by
  obtain ⟨g, hg⟩ := exists_conj_field4 (alphaA e a ha)
  obtain ⟨h1, h2⟩ := TT_invariant e a ha haT
  obtain ⟨hW1, hW2⟩ := Wof_perm (TT (T := T) e) (alphaA e a ha) g _ hg h1 h2
  exact Om_map_mem (Wof (TT (T := T) e)) (Wof_unitary _) (alphaA e a ha) g _ hg hW1 hW2 hX

theorem mem_iff_of_map_eq {X : Subgroup SU4} {f : SU4 →* SU4} (hf : Function.Injective f)
    (hX : X.map f = X) (s : SU4) : f s ∈ X ↔ s ∈ X := by
  constructor
  · intro h
    have h' : f s ∈ X.map f := by rw [hX]; exact h
    obtain ⟨s', hs', hfs⟩ := Subgroup.mem_map.1 h'
    rwa [hf hfs] at hs'
  · intro h
    have := Subgroup.mem_map_of_mem f h
    rwa [hX] at this

theorem map_alphaA_one {L : Subgroup G} (e : ↥L ≃* SU4) (Y : Subgroup SU4) {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (h : a = 1) :
    Y.map (alphaA e a ha).toMonoidHom = Y := by
  subst h
  rw [alphaA_one e ha, Subgroup.map_id]

theorem u48RootResidual_holds (G : Type) [Group G] [Finite G] :
    CFSG.LocalAnalysis.GLTheoremA.U48RootResidual G := by
  intro X L A E T hL hcat hAN hA _hEA _hEL _hE hTL hT2 hTO hAT
  let e : ↥L ≃* SU4 := lModel hcat
  have hT1 : T ≠ ⊥ := fun h => hTO (by rw [h]; exact bot_le)
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hT1 (eq_bot_iff.2 fun t ht => Subgroup.mem_bot.2 (hc t ht))
  have hT2' : IsPGroup 2 (T.subgroupOf L) := hT2.comap_subtype
  have hTT2 : IsPGroup 2 (TT (T := T) e) := hT2'.map e.toMonoidHom
  have hW2 : IsPGroup 2 (Wof (TT (T := T) e)) :=
    hTT2.map (CFSG.LieType.Universal.Unitary.SUid σ4 4).subtype
  have hs_mem : e ⟨t, hTL htT⟩ ∈ TT (T := T) e :=
    Subgroup.mem_map.2 ⟨⟨t, hTL htT⟩, Subgroup.mem_subgroupOf.2 htT, rfl⟩
  have hs_ne : (e ⟨t, hTL htT⟩ : SU4) ≠ 1 := by
    intro h
    apply ht1
    have h1 : (⟨t, hTL htT⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h1
  have hWne : Wof (TT (T := T) e) ≠ ⊥ := by
    intro hbot
    have hmem : ((e ⟨t, hTL htT⟩ : SU4) : GL (Fin 4) KF) ∈ Wof (TT (T := T) e) :=
      mem_Wof.2 ⟨_, hs_mem, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hs_ne (Subtype.ext hmem)
  have hRs : Rs (Wof (TT (T := T) e)) ≠ ⊥ := Rs_ne_bot hKF hW2 hWne (Wof_unitary _)
  have hRtot := Rs_totIso (Wof (TT (T := T) e)) (Wof_unitary _)
  have hcard : Nat.card ↥(Om (Rs (Wof (TT (T := T) e)))) % 3 ≠ 0 := by
    rcases card_Om_mod _ hRtot hRs with h | h <;> rw [h] <;> norm_num
  haveI : Finite ↥(Om (Rs (Wof (TT (T := T) e)))) := (Om_finite _).to_subtype
  letI actA : MulAction ↥A ↥(Om (Rs (Wof (TT (T := T) e)))) :=
    { smul := fun a Y => ⟨Y.1.map (alphaA e (a : G) (hAN a.2)).toMonoidHom,
        om_alphaA e (a : G) (hAN a.2) (hAT a.2) Y.2⟩
      one_smul := fun Y => Subtype.ext (map_alphaA_one e Y.1 (hAN (1 : ↥A).2) rfl)
      mul_smul := fun a b Y => Subtype.ext (by
        show Y.1.map (alphaA e ((a * b : ↥A) : G) (hAN (a * b : ↥A).2)).toMonoidHom =
          (Y.1.map (alphaA e (b : G) (hAN b.2)).toMonoidHom).map (alphaA e (a : G) (hAN a.2)).toMonoidHom
        rw [Subgroup.map_map, alphaA_toMonoidHom_congr e (show ((a * b : ↥A) : G) = (a : G) * (b : G) from rfl)
          (hAN (a * b : ↥A).2) (hAN (a * b : ↥A).2), alphaA_mul e (a : G) (b : G) (hAN a.2) (hAN b.2) (hAN (a * b : ↥A).2)]) }
  have hA3 : IsPGroup 3 ↥A := isPGroup_of_isElemAbelian hA
  obtain ⟨Y, hY⟩ := exists_fixed_of_card hA3 hcard
  obtain ⟨w, ⟨hwR, hw0⟩, hwX⟩ := Y.2
  have hiso : IsIsoVec hKF w := isoVec_of_tot (Rs_totIso _ (Wof_unitary _)) hwR hw0
  have hX0eq : Y.1 = rootSU w hiso.2 := by
    rw [← hwX, rootAny_of hiso.2]
  have hfix : ∀ a : G, (ha : a ∈ A) → Y.1.map (alphaA e a (hAN ha)).toMonoidHom = Y.1 := fun a ha =>
    congrArg Subtype.val (hY ⟨a, ha⟩)
  have hcard8 : Nat.card ↥Y.1 = 8 := by
    rw [hX0eq]
    exact card_rootSU hiso
  let RG : Subgroup G := (Y.1.map (e.symm.toMonoidHom : SU4 →* ↥L)).map L.subtype
  have memRG : ∀ h : G, h ∈ RG ↔ ∃ hh : h ∈ L, e ⟨h, hh⟩ ∈ Y.1 := by
    intro h
    constructor
    · intro hh
      obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 hh
      obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hy
      have hyeq : y = e.symm s := hsy.symm
      have hhL : h ∈ L := by
        rw [← hyh]
        exact y.2
      refine ⟨hhL, ?_⟩
      have h1 : (⟨h, hhL⟩ : ↥L) = y := Subtype.ext hyh.symm
      rw [h1, hyeq, MulEquiv.apply_symm_apply]
      exact hs
    · rintro ⟨hh, hX⟩
      exact Subgroup.mem_map.2 ⟨⟨h, hh⟩, Subgroup.mem_map.2 ⟨e ⟨h, hh⟩, hX, by simp⟩, rfl⟩
  have hnorm : ∀ a : G, a ∈ A → a ∈ Subgroup.normalizer (RG : Set G) := by
    intro a haA
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hconj : ∀ hh : h ∈ L, e ⟨a * h * a⁻¹, (Subgroup.mem_normalizer_iff.1 (hAN haA) h).1 hh⟩ =
        alphaA e a (hAN haA) (e ⟨h, hh⟩) := by
      intro hh
      rw [alphaA_apply]
      rfl
    constructor
    · intro hh
      obtain ⟨hhL, hX⟩ := (memRG h).1 hh
      have hahL := (Subgroup.mem_normalizer_iff.1 (hAN haA) h).1 hhL
      refine (memRG _).2 ⟨hahL, ?_⟩
      rw [hconj hhL]
      exact (mem_iff_of_map_eq (alphaA e a (hAN haA)).injective (hfix a haA) _).2 hX
    · intro hh
      obtain ⟨hahL, hX⟩ := (memRG _).1 hh
      have hhL := (Subgroup.mem_normalizer_iff.1 (hAN haA) h).2 hahL
      refine (memRG h).2 ⟨hhL, ?_⟩
      rw [hconj hhL] at hX
      exact (mem_iff_of_map_eq (alphaA e a (hAN haA)).injective (hfix a haA) _).1 hX
  refine ⟨RG, ?_, ?_, fun a ha => hnorm a ha, ?_⟩
  · show Nat.card ↥((Y.1.map (e.symm.toMonoidHom : SU4 →* ↥L)).map L.subtype) = 8
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective (f := (e.symm.toMonoidHom : SU4 →* ↥L)) e.symm.injective, hcard8]
  · exact Subgroup.map_subtype_le _
  · intro r hr hr1
    obtain ⟨hrL, hX⟩ := (memRG r).1 hr
    have hx : e ⟨r, hrL⟩ ∈ rootSU w hiso.2 := by
      rw [hX0eq] at hX
      exact hX
    have hx1 : e ⟨r, hrL⟩ ≠ 1 := by
      intro h
      apply hr1
      have h1 : (⟨r, hrL⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
      exact congrArg Subtype.val h1
    constructor
    · have h2 : (⟨r, hrL⟩ : ↥L) ^ 2 = 1 := e.injective (by rw [map_pow, map_one]; exact sq_rootSU hx)
      have h3 := congrArg Subtype.val h2
      simpa using h3
    · rw [isCentralIn_iff_cenIn 2 L hrL]
      have hc := CenIn.congr e.symm (cenIn_rootSU hiso hx hx1)
      rwa [MulEquiv.symm_apply_apply] at hc

end CFSG.LocalAnalysis.GLTheoremA.CatB.KU48R
