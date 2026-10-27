module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Layer
public import CFSG.LocalAnalysis.RankThreeUC.GN15LayerRel
public import CFSG.LocalAnalysis.RankThreeUC.GN15LayerK3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
import CFSG.LocalAnalysis.RankThreeUC.GN15LayerCrit
import CFSG.Quasithin.EmptyFaithful.S153DGen3
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open scoped commutatorElement

section HCon

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

private theorem conjClosure_le_gnV_aux (K : Subgroup X) :
    conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) ≤ gnV T := by
  rw [gnV_eq_conjClosure T]
  exact conjClosure_mono le_rfl le_top

private theorem toStar_comm_of_mem {a b : X} (h : a * b * a⁻¹ * b⁻¹ ∈ gnC T) :
    toStar T a * toStar T b = toStar T b * toStar T a := by
  have h1 : toStar T (a * b * a⁻¹ * b⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc toStar T a * toStar T b
      = (toStar T a * toStar T b * (toStar T a)⁻¹ * (toStar T b)⁻¹) *
          (toStar T b * toStar T a) := by group
    _ = toStar T b * toStar T a := by rw [h1, one_mul]

private theorem mem_gnC_of_toStar_comm {a b : X}
    (h : toStar T a * toStar T b = toStar T b * toStar T a) : a * b * a⁻¹ * b⁻¹ ∈ gnC T := by
  refine (QuotientGroup.eq_one_iff _).1 ?_
  show toStar T (a * b * a⁻¹ * b⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

theorem isPConstrained_three_autOn_gnKThree (hX : GNSetting X T) :
    CFSG.ABGLocalTools.IsPConstrained 3
      ↥(autOn (gnKThree T ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (gnKThree T ⊔ T))) := by
  classical
  set K : Subgroup X := gnKThree T with hKdef
  set M : Subgroup X := K ⊔ T with hMdef
  set W : Subgroup X := conjClosure (quasithinOmegaOneCenter T) M with hWdef
  have hLN : M ≤ Subgroup.normalizer (W : Set X) := le_normalizer_conjClosure _ _
  set ψ := CFSG.Quasithin.S153D.autOnHom hLN with hψ
  have hψs : Function.Surjective ψ := CFSG.Quasithin.S153D.autOnHom_surjective hLN
  have hker : ∀ m : ↥M, ψ m = 1 ↔ (m : X) ∈ Subgroup.centralizer (W : Set X) :=
    CFSG.Quasithin.S153D.autOnHom_eq_one_iff hLN
  have hCW : gnC T ≤ Subgroup.centralizer (W : Set X) :=
    Subgroup.centralizer_le (conjClosure_le_gnV_aux K)
  have hfaith := inf_centralizer_conjClosure_le hX (gnKThree_normal (T := T))
    (gnKThree_le_gnHPre (T := T))
  have hKM : (K.subgroupOf M).Normal := (gnKThree_normal (T := T)).subgroupOf M
  have hPM : ((gnPThree T).subgroupOf M).Normal := (gnPThree_normal (T := T)).subgroupOf M
  haveI hN : ((K.subgroupOf M).map ψ).Normal := Subgroup.Normal.map hKM ψ hψs
  haveI hF : (((gnPThree T).subgroupOf M).map ψ).Normal := Subgroup.Normal.map hPM ψ hψs
  have hF3 : IsPGroup 3 (((gnPThree T).subgroupOf M).map ψ) := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 3) (G := X ⧸ gnC T)) ⟨toStar T m, hm⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have h1 : (toStar T (m : X)) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 : (m : X) ^ 3 ^ n ∈ gnC T := (QuotientGroup.eq_one_iff _).1 (by
      show toStar T ((m : X) ^ 3 ^ n) = 1
      rw [map_pow]; exact h1)
    have h3 : ψ (m ^ 3 ^ n) = 1 := (hker _).2 (hCW h2)
    simpa [map_pow] using h3
  have hGN : IsPGroup 2 (↥(autOn M W) ⧸ (K.subgroupOf M).map ψ) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, rfl⟩ := hψs g
    haveI := (gnKThree_normal (T := T))
    obtain ⟨k, hk, t, ht, hkt⟩ := Subgroup.mem_sup_of_normal_left.mp m.2
    obtain ⟨n, hn⟩ := hX.sylow.2.1 ⟨t, ht⟩
    refine ⟨n, ?_⟩
    have ht1 : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    set mk : ↥M := ⟨k, Subgroup.mem_sup_left hk⟩ with hmk
    set mt : ↥M := ⟨t, Subgroup.mem_sup_right ht⟩ with hmt
    have hm : m = mk * mt := Subtype.ext hkt.symm
    have hmt1 : mt ^ 2 ^ n = 1 := Subtype.ext (by simpa using ht1)
    have hk1 : (QuotientGroup.mk (ψ mk) : ↥(autOn M W) ⧸ (K.subgroupOf M).map ψ) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨mk, hk, rfl⟩
    have hq : (QuotientGroup.mk (ψ m) : ↥(autOn M W) ⧸ (K.subgroupOf M).map ψ) =
        QuotientGroup.mk (ψ mt) := by
      rw [hm, map_mul, QuotientGroup.mk_mul, hk1, one_mul]
    rw [hq, ← QuotientGroup.mk_pow, ← map_pow, hmt1, map_one, QuotientGroup.mk_one]
  have hlift : ∀ x ∈ (K.subgroupOf M).map ψ ⊓ Subgroup.centralizer
      ((((gnPThree T).subgroupOf M).map ψ : Subgroup ↥(autOn M W)) : Set ↥(autOn M W)),
      ∃ m : ↥M, (m : X) ∈ K ∧ ψ m = x ∧
        ∀ p ∈ CFSG.pCore 3 (X ⧸ gnC T), p * toStar T (m : X) = toStar T (m : X) * p := by
    rintro x ⟨⟨m, hm, rfl⟩, hxc⟩
    refine ⟨m, hm, rfl, fun p hp => ?_⟩
    obtain ⟨p', rfl⟩ := QuotientGroup.mk'_surjective (gnC T) p
    have hp'P : p' ∈ gnPThree T := hp
    have hp'K : p' ∈ K := gnPThree_le_gnKThree hp'P
    set pm : ↥M := ⟨p', Subgroup.mem_sup_left hp'K⟩ with hpm
    have hmem : ψ pm ∈ ((gnPThree T).subgroupOf M).map ψ := ⟨pm, hp'P, rfl⟩
    have hc : ψ pm * ψ m = ψ m * ψ pm := Subgroup.mem_centralizer_iff.1 hxc _ hmem
    have h1 : ψ (pm * m * pm⁻¹ * m⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have hmK : (m : X) ∈ K := hm
    have hprod : ((pm * m * pm⁻¹ * m⁻¹ : ↥M) : X) = p' * (m : X) * p'⁻¹ * (m : X)⁻¹ := rfl
    have h2 : p' * (m : X) * p'⁻¹ * (m : X)⁻¹ ∈ K ⊓ Subgroup.centralizer (W : Set X) :=
      ⟨K.mul_mem (K.mul_mem (K.mul_mem hp'K hmK) (K.inv_mem hp'K)) (K.inv_mem hmK), by
        have := (hker _).1 h1
        rwa [hprod] at this⟩
    exact toStar_comm_of_mem (a := p') (b := (m : X)) (hfaith h2)
  have hab : ∀ x ∈ (K.subgroupOf M).map ψ ⊓ Subgroup.centralizer
      ((((gnPThree T).subgroupOf M).map ψ : Subgroup ↥(autOn M W)) : Set ↥(autOn M W)),
      ∀ y ∈ (K.subgroupOf M).map ψ ⊓ Subgroup.centralizer
      ((((gnPThree T).subgroupOf M).map ψ : Subgroup ↥(autOn M W)) : Set ↥(autOn M W)),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, hmK, rfl, hmP⟩ := hlift x hx
    obtain ⟨m', hm'K, rfl, hm'P⟩ := hlift y hy
    have hcomm := commute_toStar_of_mem_gnKThree hmK hm'K hmP hm'P
    have hc : ψ (m * m' * m⁻¹ * m'⁻¹) = 1 := by
      rw [hker]
      exact hCW (by simpa using mem_gnC_of_toStar_comm hcomm)
    calc ψ m * ψ m' = ψ (m * m' * m⁻¹ * m'⁻¹) * (ψ m' * ψ m) := by
          simp only [map_mul, map_inv]; group
      _ = ψ m' * ψ m := by rw [hc, one_mul]
  exact isPConstrained_three_of_two_quotient hF3 hGN hab

end HCon

section Commutator

private theorem mul_comm_of_mem_sup_aux {G : Type} [Group G] {A B : Subgroup G} {z : G}
    (hA : ∀ a ∈ A, a * z = z * a) (hB : ∀ b ∈ B, b * z = z * b) :
    ∀ g ∈ A ⊔ B, g * z = z * g := fun g hg => by
  have h : A ⊔ B ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hA a ha))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB b hb))
  exact Subgroup.mem_centralizer_singleton_iff.1 (h hg)

private theorem commutator_mem_centralizer_sup {G : Type} [Group G] {E W : Subgroup G}
    [E.Normal] [W.Normal] {h j : G} (hh : h ∈ Subgroup.centralizer (E : Set G))
    (hj : j ∈ Subgroup.centralizer (W : Set G)) :
    ⁅h, j⁆ ∈ Subgroup.centralizer ((E ⊔ W : Subgroup G) : Set G) := by
  haveI : (Subgroup.centralizer (E : Set G)).Normal := Subgroup.normal_centralizer
  haveI : (Subgroup.centralizer (W : Set G)).Normal := Subgroup.normal_centralizer
  have hE : ⁅h, j⁆ ∈ Subgroup.centralizer (E : Set G) := by
    have h1 : j * h⁻¹ * j⁻¹ ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.Normal.conj_mem inferInstance h⁻¹ (inv_mem hh) j
    have : ⁅h, j⁆ = h * (j * h⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem hh h1
  have hW : ⁅h, j⁆ ∈ Subgroup.centralizer (W : Set G) := by
    have h1 : h * j * h⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
      Subgroup.Normal.conj_mem inferInstance j hj h
    have : ⁅h, j⁆ = (h * j * h⁻¹) * j⁻¹ := by rw [commutatorElement_def]
    rw [this]
    exact mul_mem h1 (inv_mem hj)
  exact Subgroup.mem_centralizer_iff.2 (mul_comm_of_mem_sup_aux (Subgroup.mem_centralizer_iff.1 hE)
    (Subgroup.mem_centralizer_iff.1 hW))

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem commutator_mem_gnKThree (hJ3 : ThreePrimeJCentral) (hX : GNSetting X T) {h j : X}
    (hh : h ∈ gnHPre T) (hj : j ∈ thompsonJ T) : ⁅h, j⁆ ∈ gnKThree T := by
  haveI : (rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T))).Normal := by
    have h := CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_rankThreeLayer
      (⊤ : Subgroup (X ⧸ gnC T))
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)
  have hW : CFSG.pPrimeCore 3 (X ⧸ gnC T) ≤
      Subgroup.centralizer ((gnImg T (thompsonJ T) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (hJ3 X T hX _ inferInstance CFSG.pPrimeCore_coprime_card)
  have hjW : toStar T j ∈ Subgroup.centralizer
      ((CFSG.pPrimeCore 3 (X ⧸ gnC T) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 (hW hw) (toStar T j) ⟨j, hj, rfl⟩).symm
  have hh' : toStar T h ∈ Subgroup.centralizer
      ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := hh
  have := commutator_mem_centralizer_sup hh' hjW
  rw [← map_commutatorElement] at this
  exact this

theorem gnKMin_le_gnKThree (hJ3 : ThreePrimeJCentral) (hX : GNSetting X T) :
    gnKMin T ≤ gnKThree T :=
  Subgroup.normalClosure_le_normal (N := gnKThree T)
    (Subgroup.commutator_le.2 fun _ hh _ hj => commutator_mem_gnKThree hJ3 hX hh hj)

end Commutator

section Y0

variable {X : Type} [Group X] {T T₁ T₂ : Subgroup X}

private theorem isComponentOf_conjSub_aux {G : Type*} [Group G] {L : Subgroup G}
    (hL : IsComponentOf L ⊤) (g : G) : IsComponentOf (B6.conjSub g L) ⊤ :=
  (CFSG.isComponent_iff_open _).1
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g)
      ((CFSG.isComponent_iff_open L).2 hL))

private theorem conj_mem_Y0 {g : X} (h1 : g ∈ Subgroup.normalizer (T₁ : Set X))
    (h2 : g ∈ Subgroup.normalizer (T₂ : Set X)) {y : X} (hy : y ∈ Y0 T T₁ T₂) :
    g * y * g⁻¹ ∈ Y0 T T₁ T₂ := by
  have hA : toStar T g ∈ Subgroup.normalizer
      ((gnImg T (Subgroup.centralizer (T₁ : Set X)) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    Subgroup.le_normalizer_map (toStar T)
      ⟨g, CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup T₁ h1, rfl⟩
  have hB : toStar T g ∈ Subgroup.normalizer
      ((gnImg T (Subgroup.normalizer (T₂ : Set X)) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) :=
    Subgroup.le_normalizer_map (toStar T) ⟨g, Subgroup.le_normalizer h2, rfl⟩
  have hconj : ∀ L, GNYComponent T T₁ T₂ L →
      GNYComponent T T₁ T₂ (B6.conjSub (toStar T g) L) := by
    rintro L ⟨hL, hLA, hLB⟩
    refine ⟨isComponentOf_conjSub_aux hL _, fun h => hLA ?_, fun h => hLB ?_⟩
    · have h' : B6.conjSub (toStar T g) L ≤ B6.conjSub (toStar T g)
          (gnImg T (Subgroup.centralizer (T₁ : Set X))) := by
        rwa [B6.conjSub_eq_self hA]
      exact (B6.conjSub (toStar T g)).le_iff_le.1 h'
    · have h' : B6.conjSub (toStar T g) L ≤ B6.conjSub (toStar T g)
          (gnImg T (Subgroup.normalizer (T₂ : Set X))) := by
        rwa [B6.conjSub_eq_self hB]
      exact (B6.conjSub (toStar T g)).le_iff_le.1 h'
  have hYst : B6.conjSub (toStar T g) (Ystar T T₁ T₂) ≤ Ystar T T₁ T₂ := by
    unfold Ystar
    simp only [OrderIso.map_iSup]
    exact iSup₂_le fun L hL => le_iSup₂_of_le (B6.conjSub (toStar T g) L) (hconj L hL) le_rfl
  have hy' : toStar T y ∈ Ystar T T₁ T₂ := hy
  have hmem : toStar T (g * y * g⁻¹) ∈ B6.conjSub (toStar T g) (Ystar T T₁ T₂) := by
    rw [B6.mem_conjSub]
    have : (toStar T g)⁻¹ * toStar T (g * y * g⁻¹) * toStar T g = toStar T y := by
      simp only [map_mul, map_inv]; group
    rw [this]
    exact hy'
  exact hYst hmem

theorem mem_normalizer_Y0 {g : X} (h1 : g ∈ Subgroup.normalizer (T₁ : Set X))
    (h2 : g ∈ Subgroup.normalizer (T₂ : Set X)) : g ∈ Subgroup.normalizer (Y0 T T₁ T₂ : Set X) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => conj_mem_Y0 h1 h2 hy, fun hy => ?_⟩
  have := conj_mem_Y0 (T := T) ((Subgroup.normalizer (T₁ : Set X)).inv_mem h1)
    ((Subgroup.normalizer (T₂ : Set X)).inv_mem h2) hy
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at this

theorem gnT_le_normalizer_Y0 (hP : IsC118Pair T T₁ T₂) :
    T ≤ Subgroup.normalizer (Y0 T T₁ T₂ : Set X) := by
  obtain ⟨-, h1Z, h1c, -, h2B, h2c, -⟩ := hP
  intro g hg
  have hT1 : T₁ ≤ T := (h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)).trans (C1GN.baum_le T)
  refine mem_normalizer_Y0 (T := T) ?_ ?_
  · exact normalizer_le_normalizer_of_characteristic_subgroupOf hT1 h1c (Subgroup.le_normalizer hg)
  · exact normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2c
      (normalizer_le_normalizer_baum T (Subgroup.le_normalizer hg))

private theorem Ystar_le_layer : Ystar T T₁ T₂ ≤ rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) :=
  iSup₂_le fun _ hL => le_sSup hL.1

theorem gnHPre_le_normalizer_Y0 : gnHPre T ≤ Subgroup.normalizer (Y0 T T₁ T₂ : Set X) := by
  have key : ∀ h ∈ gnHPre T, ∀ y ∈ Y0 T T₁ T₂, h * y * h⁻¹ ∈ Y0 T T₁ T₂ := by
    intro h hh y hy
    have hy' : toStar T y ∈ Ystar T T₁ T₂ := hy
    have hh' : toStar T h ∈ Subgroup.centralizer
        ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := hh
    have hc : toStar T y * toStar T h = toStar T h * toStar T y :=
      Subgroup.mem_centralizer_iff.1 hh' (toStar T y) (Ystar_le_layer hy')
    show toStar T (h * y * h⁻¹) ∈ Ystar T T₁ T₂
    have : toStar T (h * y * h⁻¹) = toStar T y := by
      rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right]
    rw [this]
    exact hy'
  intro h hh
  refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => key h hh y hy, fun hy => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hy
  have e : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
  rwa [e] at this

end Y0

section Final

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem gnLayerFactor_of (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) : GNLayerFactor T T₁ T₂ := by
  intro k hk
  have hkK : k ∈ gnKThree T := gnKMin_le_gnKThree hJ3 hX hk
  obtain ⟨a, ha, b, hb, hab⟩ := factor_of_threeConstrained_rel hI59 hX hP
    (gnKThree_normal (T := T)) (isPConstrained_three_autOn_gnKThree hX) k
    (Subgroup.mem_sup_left hkK)
  refine ⟨a, ha.1, b, hb.1, ?_, hab⟩
  exact sup_le (gnKThree_le_gnHPre.trans gnHPre_le_normalizer_Y0) (gnT_le_normalizer_Y0 hP) hb.2

theorem gnAbsorbs_H (hI59 : AGL81I59) (hJ3 : ThreePrimeJCentral) (hX : GNSetting X T)
    (hP : IsC118Pair T T₁ T₂) : GNAbsorbs T T₁ T₂ (gnHPre T) :=
  gnAbsorbs_H_of_layerFactor hX hP (gnLayerFactor_of hI59 hJ3 hX hP)

end Final

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
