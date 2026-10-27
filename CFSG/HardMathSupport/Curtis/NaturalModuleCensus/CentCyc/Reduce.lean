module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBar
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.EvenCentre
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open scoped commutatorElement

section Levi

variable {Y : Type*} [Group Y] {L J : Subgroup Y}

theorem exists_mul_of_mem_sup_commute {A B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup Y :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem mk_eq_one_iff_mem_centralizer {j : Y} (hj : j ∈ L) :
    (QuotientGroup.mk ⟨j, hj⟩ : ↥L ⧸ Subgroup.center ↥L) = 1 ↔
      j ∈ Subgroup.centralizer (L : Set Y) := by
  rw [← QuotientGroup.mk_one, QuotientGroup.eq, mul_one, inv_mem_iff,
    Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hg⟩)
  · intro h g
    exact Subtype.ext (h g g.2)

theorem exists_leviHom (hJL : J ≤ L) :
    ∃ ρ : ↥(J ⊔ Subgroup.centralizer (L : Set Y)) →* ↥L ⧸ Subgroup.center ↥L,
      (∀ (j : Y) (hj : j ∈ J) (c : Y) (hc : c ∈ Subgroup.centralizer (L : Set Y)),
        ρ ⟨j * c, Subgroup.mul_mem_sup hj hc⟩ = QuotientGroup.mk ⟨j, hJL hj⟩) ∧
      ∀ g : ↥(J ⊔ Subgroup.centralizer (L : Set Y)),
        ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (L : Set Y) := by
  set C : Subgroup Y := Subgroup.centralizer (L : Set Y) with hC
  have hcomm : ∀ (j : ↥J) (c : ↥C), Commute (J.subtype j) (C.subtype c) := fun j c =>
    Subgroup.mem_centralizer_iff.1 c.2 j (hJL j.2)
  let Φ : ↥J × ↥C →* Y := MonoidHom.noncommCoprod J.subtype C.subtype hcomm
  have hΦrange : Φ.range = J ⊔ C := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hΦmem : ∀ q, Φ q ∈ J ⊔ C := fun q => by
    rw [← hΦrange]
    exact ⟨q, rfl⟩
  let Φ' : ↥J × ↥C →* ↥(J ⊔ C) := Φ.codRestrict _ hΦmem
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hΦrange] at hy
    obtain ⟨q, hq⟩ := hy
    exact ⟨q, Subtype.ext hq⟩
  let f : ↥J × ↥C →* ↥L ⧸ Subgroup.center ↥L :=
    (QuotientGroup.mk' _).comp ((Subgroup.inclusion hJL).comp (MonoidHom.fst _ _))
  have hfq : ∀ q : ↥J × ↥C, f q = QuotientGroup.mk ⟨(q.1 : Y), hJL q.1.2⟩ := fun q => rfl
  have hΦ'q : ∀ q : ↥J × ↥C, ((Φ' q : ↥(J ⊔ C)) : Y) = (q.1 : Y) * (q.2 : Y) := fun q => rfl
  have hker : Φ'.ker ≤ f.ker := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq ⊢
    have h1 : (q.1 : Y) * (q.2 : Y) = 1 := by
      rw [← hΦ'q q, hq]
      rfl
    rw [hfq, mk_eq_one_iff_mem_centralizer]
    have : (q.1 : Y) = ((q.2 : Y))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.inv_mem _ q.2.2
  let ρ := (Φ'.liftOfSurjective hΦ'surj) ⟨f, hker⟩
  have hρ : ∀ q, ρ (Φ' q) = f q := fun q => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨ρ, ?_, ?_⟩
  · intro j hj c hc
    have := hρ (⟨j, hj⟩, ⟨c, hc⟩)
    rw [hfq] at this
    exact this
  · intro g
    obtain ⟨q, rfl⟩ := hΦ'surj g
    rw [hρ, hfq, mk_eq_one_iff_mem_centralizer, hΦ'q]
    constructor
    · intro h
      exact Subgroup.mul_mem _ h q.2.2
    · intro h
      have : (q.1 : Y) = ((q.1 : Y) * (q.2 : Y)) * ((q.2 : Y))⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ q.2.2)

end Levi

section Parab

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}

abbrev jBar (L J : Subgroup Y) : Subgroup (↥L ⧸ Subgroup.center ↥L) :=
  (J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))

theorem exists_sylow_normalizer_subgroupOf_of_compParabE (h : CompParabE L J) :
    ∃ T : Subgroup ↥L, IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set ↥L) ≤ J.subgroupOf L ∧
      J.subgroupOf L ≠ Subgroup.normalizer (T : Set ↥L) := by
  have hJL : J ≤ L := h.parab.1
  obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := h.parab
  refine ⟨T.subgroupOf L, ⟨le_top, hT2.comap_subtype (K := L), ?_⟩, ?_, ?_⟩
  · have e : ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index :=
      Subgroup.relIndex_top_right _
    rw [e]
    exact hTi
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
    have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
    simpa [Subgroup.mem_subgroupOf] using h2
  · intro hJe
    apply h.ne_borel T ⟨hTL, hT2, hTi⟩
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hyL : y ∈ L := hJL hy
      refine ⟨hyL, ?_⟩
      have hyG : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
      rw [hJe] at hyG
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hyG ⟨t, hTL ht⟩).1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · obtain ⟨hyL, hyN⟩ := hy
      have : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := by
        rw [hJe, Subgroup.mem_normalizer_iff]
        intro g
        have := Subgroup.mem_normalizer_iff.1 hyN g.1
        simp only [Subgroup.mem_subgroupOf]
        exact this
      exact Subgroup.mem_subgroupOf.1 this

theorem center_le_subgroupOf_of_isParabolicTwo (hP : IsParabolicTwo L J) :
    Subgroup.center ↥L ≤ J.subgroupOf L := by
  obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  refine hNJ ⟨z.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
  have h1 : (⟨t, hTL ht⟩ : ↥L) * z = z * ⟨t, hTL ht⟩ := Subgroup.mem_center_iff.1 hz _
  have h2 : (z : Y) * t * (z : Y)⁻¹ = t := by
    have := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at this
    rw [← this]
    group
  rw [h2]
  exact ht

theorem exists_sylow_parab_central (h : CompParabE L J) :
    ∃ S₀ : Sylow 2 (↥L ⧸ Subgroup.center ↥L),
      Subgroup.normalizer ((S₀ : Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set _) ≤ jBar L J ∧
      jBar L J ≠ Subgroup.normalizer ((S₀ : Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set _) ∧
      jBar L J ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ, hneB⟩ := exists_sylow_normalizer_subgroupOf_of_compParabE h
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  let T' : Sylow 2 ↥L := hT.2.1.toSylow hidx
  have hT'T : (T' : Subgroup ↥L) = T := rfl
  set ψ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hψdef
  have hψ : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  have hker : ψ.ker ≤ Subgroup.center ↥L := (QuotientGroup.ker_mk' _).le
  have hNJ' : Subgroup.normalizer ((T' : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := hNJ
  have hkJ : ψ.ker ≤ J.subgroupOf L :=
    hker.trans ((Subgroup.center_le_normalizer ((T' : Subgroup ↥L) : Set ↥L)).trans hNJ')
  refine ⟨T'.mapSurjective hψ, ?_, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective hψ T']
    exact normalizer_map_le_map_of_central ψ hψ hker T' hNJ'
  · intro hJe
    apply hneB
    refine le_antisymm (fun x hx => ?_) hNJ
    have hJe' : (J.subgroupOf L).map ψ =
        Subgroup.normalizer (((T' : Subgroup ↥L).map ψ : Subgroup _) : Set _) := by
      rw [← Sylow.coe_mapSurjective hψ T']
      exact hJe
    have hmem : ψ x ∈ Subgroup.normalizer (((T' : Subgroup ↥L).map ψ : Subgroup _) : Set _) := by
      rw [← hJe']
      exact ⟨x, hx, rfl⟩
    exact mem_normalizer_of_map_mem_normalizer ψ hker T' hmem
  · intro htop
    have hcomap : ((J.subgroupOf L).map ψ).comap ψ = J.subgroupOf L :=
      Subgroup.comap_map_eq_self hkJ
    have h1 : J.subgroupOf L = ⊤ := by
      have htop' : (J.subgroupOf L).map ψ = ⊤ := htop
      rw [← hcomap, htop', Subgroup.comap_top]
    exact h.ne_top (le_antisymm h.parab.1 (Subgroup.subgroupOf_eq_top.1 h1))

theorem exists_perfect_lift_le (hP : IsParabolicTwo L J)
    {V : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hV : ⁅V, V⁆ = V) (hVJ : V ≤ jBar L J) :
    ∃ W : Subgroup Y, W ≤ J ∧ ⁅W, W⁆ = W ∧
      (W.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) = V := by
  set ψ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hψdef
  have hker : ψ.ker ≤ Subgroup.center ↥L := (QuotientGroup.ker_mk' _).le
  have hkJ : ψ.ker ≤ J.subgroupOf L := hker.trans (center_le_subgroupOf_of_isParabolicTwo hP)
  have hcomap : ((J.subgroupOf L).map ψ).comap ψ = J.subgroupOf L :=
    Subgroup.comap_map_eq_self hkJ
  obtain ⟨W', hW', hWle, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
    (by rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hW'J : W' ≤ J.subgroupOf L := by
    refine hWle.trans ?_
    rw [← hcomap]
    exact Subgroup.comap_mono hVJ
  have hsub : (W'.map L.subtype).subgroupOf L = W' := by
    ext w
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  refine ⟨W'.map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hW'J hw)
  · rw [← Subgroup.map_commutator, hW']
  · rw [hsub]
    exact hWmap

end Parab

section Trivial

variable {Y : Type*} [Group Y] {L : Subgroup Y}

theorem perfect_cent_trivial_one {x : Y} {l : ↥L} {c : Y}
    (hc : c ∈ Subgroup.centralizer (L : Set Y)) (hx : x = (l : Y) * c)
    (hxW : ∀ W : Subgroup Y, W ≤ L → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) →
      W = ⊥)
    {V : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hVC : V ≤ Subgroup.centralizer ({(QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L)} :
      Set (↥L ⧸ Subgroup.center ↥L)))
    (hV : ⁅V, V⁆ = V) : V = ⊥ := by
  set ψ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hψdef
  have hker : ψ.ker ≤ Subgroup.center ↥L := (QuotientGroup.ker_mk' _).le
  obtain ⟨W', hW', -, hWmap⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker hV
    (by rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hcentral : ∀ w ∈ W', ⁅w, l⁆ ∈ Subgroup.center ↥L := by
    intro w hw
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have hwV : ψ w ∈ V := by rw [← hWmap]; exact ⟨w, hw, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 (hVC hwV) (ψ l) (Set.mem_singleton _)).symm
  have hW'C : W' ≤ Subgroup.centralizer ({l} : Set ↥L) := by
    rw [← hW']
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := commutator_commutator_eq_one_of_central (hcentral a ha) (hcentral b hb)
    rw [commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm
  have hbot : W'.map L.subtype = ⊥ := by
    apply hxW
    · rintro _ ⟨w, -, rfl⟩
      exact w.2
    · rw [← Subgroup.map_commutator, hW']
    · rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh, hx]
      have h1 : l * w = w * l := Subgroup.mem_centralizer_iff.1 (hW'C hw) l (Set.mem_singleton _)
      have h2 : (w : Y) * c = c * w := Subgroup.mem_centralizer_iff.1 hc w w.2
      have h1' : (l : Y) * w = w * l := congrArg Subtype.val h1
      calc (l : Y) * c * w = l * (c * w) := by group
        _ = l * (w * c) := by rw [h2]
        _ = (l * w) * c := by group
        _ = (w * l) * c := by rw [h1']
        _ = w * (l * c) := by group
  have hW'bot : W' = ⊥ := by
    refine eq_bot_iff.2 fun w hw => ?_
    have : L.subtype w ∈ W'.map L.subtype := ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  rw [← hWmap, hW'bot, Subgroup.map_bot]

end Trivial

section Bar

structure CentCycBar {X : Type*} [Group X] [Finite X] (J : Subgroup X) (p : ℕ) (v : X) :
    Prop where
  parab : ∃ S₀ : Sylow 2 X, Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ≤ J ∧
    J ≠ Subgroup.normalizer ((S₀ : Subgroup X) : Set X)
  ne_top : J ≠ ⊤
  cyc : CycPerfect p J
  pow : v ^ p = 1
  ne_one : v ≠ 1
  join : v ∈ perfectJoin J
  triv : ∀ V : Subgroup X, V ≤ Subgroup.centralizer ({v} : Set X) → ⁅V, V⁆ = V → V = ⊥

variable {X : Type*} [Group X] [Finite X] {J : Subgroup X} {p : ℕ} {v : X}

theorem CentCycBar.toFixBarData (h : CentCycBar J p v) : FixBarData J p v := by
  obtain ⟨S₀, hS₀, hne⟩ := h.parab
  refine ⟨⟨(S₀ : Subgroup X), isSylowTwoOf_top_of_sylow' S₀, hS₀, hne⟩, h.ne_top, h.cyc, h.pow,
    h.ne_one, h.join, fun V hVC hV => ?_⟩
  rw [h.triv V hVC hV]
  exact bot_le

theorem CentCycBar.triv_conj (h : CentCycBar J p v) (g : X) (V : Subgroup X)
    (hVC : V ≤ Subgroup.centralizer ({g * v * g⁻¹} : Set X)) (hV : ⁅V, V⁆ = V) : V = ⊥ := by
  let e : X →* X := (MulAut.conj g⁻¹).toMonoidHom
  have hV' : ⁅V.map e, V.map e⁆ = V.map e := by
    rw [← Subgroup.map_commutator, hV]
  have hVC' : V.map e ≤ Subgroup.centralizer ({v} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    have h1 : (g * v * g⁻¹) * y = y * (g * v * g⁻¹) :=
      Subgroup.mem_centralizer_iff.1 (hVC hy) _ (Set.mem_singleton _)
    have he : e y = g⁻¹ * y * g := by simp [e]
    rw [hk, he]
    calc v * (g⁻¹ * y * g) = g⁻¹ * ((g * v * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * v * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * y * g) * v := by group
  have hbot := h.triv _ hVC' hV'
  refine eq_bot_iff.2 fun y hy => ?_
  have : e y ∈ V.map e := ⟨y, hy, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  have h1 : g⁻¹ * y * g = 1 := by
    have he : e y = g⁻¹ * y * g := by simp [e]
    rw [← he]
    exact this
  rw [Subgroup.mem_bot]
  calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem CentCycBar.map_mulEquiv {X' : Type*} [Group X'] [Finite X'] (e : X ≃* X')
    (h : CentCycBar J p v) : CentCycBar (J.map e.toMonoidHom) p (e v) := by
  have hF := h.toFixBarData.map_mulEquiv e
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, hF.ne_top, hF.cyc, hF.pow, hF.ne_one, hF.join, ?_⟩
  · obtain ⟨S₀, hS₀, hne⟩ := h.parab
    refine ⟨S₀.mapSurjective (f := e.toMonoidHom) e.surjective, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S₀]
      rw [← Subgroup.map_normalizer_eq_of_bijective (S₀ : Subgroup X) e.bijective]
      exact Subgroup.map_mono hS₀
    · intro heq
      apply hne
      rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S₀,
        ← Subgroup.map_normalizer_eq_of_bijective (S₀ : Subgroup X) e.bijective] at heq
      exact Subgroup.map_injective hinj heq
  · intro V hVC hV
    have hVc : V.map e.symm.toMonoidHom ≤ Subgroup.centralizer ({v} : Set X) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have := Subgroup.mem_centralizer_iff.1 (hVC hy) (e g) (by simp)
      apply e.injective
      simpa using this
    have hVp : ⁅V.map e.symm.toMonoidHom, V.map e.symm.toMonoidHom⁆ =
        V.map e.symm.toMonoidHom := by
      rw [← Subgroup.map_commutator, hV]
    have := h.triv _ hVc hVp
    rw [← map_map_symm e V, this, Subgroup.map_bot]

end Bar

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
