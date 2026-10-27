module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEHyp21
public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup
import CFSG.Quasithin.Background.B2Factorization
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepESylow
import CFSG.GroupTheory.CentralizerNormalPQuotient

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet IsPStar)
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem ne_bot_of_isNatL2Section_eoff {A : Type*} [Group A] {K C W₁ W₀ : Subgroup A}
    {n : ℕ} (hn : 1 ≤ n) (h : IsNatL2Section K C W₁ W₀ n) : W₁ ≠ ⊥ := by
  intro hbot
  obtain ⟨F, hF, hFf, hFcard, rest⟩ := h
  have : Field F := hF
  have : Fintype F := hFf
  obtain ⟨-, -, -, β, hβs, -, -⟩ := rest
  have : Subsingleton ↥W₁ := by
    rw [hbot]
    exact ⟨fun a b => Subtype.ext (by
      rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩
  have hsub : Subsingleton (Multiplicative (Fin 2 → F)) := Function.Surjective.subsingleton hβs
  have h2 : 1 < @Fintype.card F hFf := by
    rw [hFcard]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Nontrivial F := (@Fintype.one_lt_card_iff_nontrivial F hFf).mp h2
  have : Nontrivial (Multiplicative (Fin 2 → F)) := inferInstance
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (Multiplicative (Fin 2 → F))).exists_pair_ne
  exact hxy (hsub.elim x y)

private theorem isPStar_of_isFFStarMin_eoff {V : Type} [CommGroup V] {X A : Subgroup (MulAut V)}
    (h : IsFFStarMin X A) : IsPStar X A := by
  refine ⟨h.1, fun B hB hBA heq => ?_⟩
  exact h.2 B hB ⟨hB.isA2, h.1.isA2, hBA, heq.symm⟩

omit [Finite Ω] in
private theorem gomiV_le_pCoreOf_eoff (G : Subgroup Ω) : gomiV G ≤ pCoreOf 2 G :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1.1

private theorem pCoreOf_le_of_isSylowTwoOf_eoff {G T : Subgroup Ω} (hT : IsSylowTwoOf T G) :
    pCoreOf 2 G ≤ T :=
  CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT

private theorem isFFStarOffender_autOn_eoff {G T A : Subgroup Ω}
    (hVT : gomiV G ≤ T) (hTN : T ≤ Subgroup.normalizer (gomiV G : Set Ω))
    (hA : IsMaxElemAbelian T A) (hA1 : ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω)) :
    IsFFStarOffender (autOn T (gomiV G)) (autOn A (gomiV G)) := by
  refine ⟨CFSG.Quasithin.AutOn.autOn_mono hA.1, ?_, ?_, ?_⟩
  · exact CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer (hA.1.trans hTN) hA1
  · exact CFSG.Quasithin.isElemAbelian2_autOn (gomiV_moduleSetting G).1 hA.2.1 (hA.1.trans hTN)
  · intro B hB
    exact (offender_core (V := gomiV G) (H := T) (gomiV_moduleSetting G).1 hVT hTN hA hB).1

theorem pstarSet_nonempty_of_isSylowIn
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {S : Subgroup (MulAut ↥(gomiV G))} (hS : IsSylowIn 2 S (autOn G (gomiV G))) :
    (PstarSet S).Nonempty := by
  obtain ⟨T, hT, hTS⟩ := exists_isSylowTwoOf_autOn_eq hS
  obtain ⟨X, hX⟩ := h45 T hT
  have hVT : gomiV G ≤ T := (gomiV_le_pCoreOf_eoff G).trans (pCoreOf_le_of_isSylowTwoOf_eoff hT)
  have hTN : T ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    hT.1.trans (gomiV_moduleSetting G).2
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
    intro hJle
    have hJleQ : thompsonJ T ≤ pCoreOf 2 G := by
      rw [← hCQ]
      exact le_inf ((thompsonJ_le_self T).trans hT.1) hJle
    have hXleV : X ≤ gomiV G := by
      calc X = ⁅X, thompsonJ T⁆ := hX.eq_commutator_thompsonJ
        _ ≤ ⁅X, pCoreOf 2 G⁆ := Subgroup.commutator_mono le_rfl hJleQ
        _ = ⁅pCoreOf 2 G, X⁆ := Subgroup.commutator_comm X (pCoreOf 2 G)
        _ ≤ gomiV G := hX.commutator_pCoreOf_le
    have hVV : ⁅gomiV G, gomiV G⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
    have hVXbot : ⁅gomiV G, X⁆ = ⊥ :=
      eq_bot_iff.mpr (hVV ▸ Subgroup.commutator_mono le_rfl hXleV)
    obtain ⟨C, n, hn, hnat⟩ := hX.natural
    exact ne_bot_of_isNatL2Section_eoff hn hnat hVXbot
  obtain ⟨A, hA, hA1⟩ : ∃ A : Subgroup Ω, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
    by_contra h
    exact hJ (iSup₂_le fun A hA => by
      by_contra hAC
      exact h ⟨A, hA, hAC⟩)
  have hĀoff : IsFFStarOffender S (autOn A (gomiV G)) := by
    rw [← hTS]
    exact isFFStarOffender_autOn_eoff hVT hTN hA hA1
  obtain ⟨B, hmin, -⟩ := CFSG.Quasithin.B1Red.exists_isFFStarMin_below hĀoff
  exact ⟨B, isPStar_of_isFFStarMin_eoff hmin⟩

private theorem isPStar_map_conj_eoff {V : Type} [CommGroup V] {X A : Subgroup (MulAut V)}
    (hA : IsPStar X A) {g : MulAut V} (hg : g ∈ X) :
    IsPStar X (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨isFFStarOffender_map_conj hA.1 hg, fun B hB hBA heq => ?_⟩
  have hB0off : IsFFStarOffender X (B.map (MulAut.conj g⁻¹).toMonoidHom) :=
    isFFStarOffender_map_conj hB (X.inv_mem hg)
  have hB0A : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
    rintro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp (hBA hb)
    have h1 : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom a) = a := by
      ext v
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hae, h1]
    exact ha
  have hcard : ∀ C : Subgroup (MulAut V),
      Nat.card (C.map (MulAut.conj g).toMonoidHom) *
        Nat.card (fixV (C.map (MulAut.conj g).toMonoidHom)) =
      Nat.card C * Nat.card (fixV C) := fun C => by
    rw [fixV_map_conj_eq, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective g.injective]
  have hcomp_inv : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (MulAut V) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have heq0 : Nat.card A * Nat.card (fixV A) =
      Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) *
        Nat.card (fixV (B.map (MulAut.conj g⁻¹).toMonoidHom)) := by
    have h1 := hcard A
    have h2 : Nat.card B * Nat.card (fixV B) =
        Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) *
          Nat.card (fixV (B.map (MulAut.conj g⁻¹).toMonoidHom)) := by
      have h2' := hcard (B.map (MulAut.conj g⁻¹).toMonoidHom)
      rw [Subgroup.map_map, hcomp_inv, Subgroup.map_id] at h2'
      exact h2'
    exact h1.symm.trans (heq.trans h2)
  have hB0eqA := hA.2 _ hB0off hB0A heq0
  calc B = (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        simp only [Subgroup.map_map, hcomp_inv, Subgroup.map_id]
    _ = A.map (MulAut.conj g).toMonoidHom := by rw [hB0eqA]

private theorem commutator_subgroupOf_eoff {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)}
    {K P : Subgroup (MulAut V)} (h : ⁅K, P⁆ = ⊥) :
    ⁅K.subgroupOf Y, P.subgroupOf Y⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_subgroupOf.mp hk))
    p.val (Subgroup.mem_subgroupOf.mp hp))

private theorem isPGroup_two_of_isElemAbelian2_eoff {V : Type} [CommGroup V]
    {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) : IsPGroup 2 A := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro a
  exact ⟨1, Subtype.ext (by simpa using h.2 a a.2)⟩

private theorem subgroupOf_le_centralizer_normalClosure_eoff {V : Type} [CommGroup V]
    {Y : Subgroup (MulAut V)} {S P : Subgroup (MulAut V)} {Bb : Subgroup ↥Y}
    (hSP : S ≤ Subgroup.normalizer (P : Set (MulAut V)))
    (hcommY : ⁅Bb, P.subgroupOf Y⁆ = ⊥)
    (hNnorm : Subgroup.normalClosure (Bb : Set ↥Y) ≤ Subgroup.normalizer (Bb : Set ↥Y))
    (htop : (⊤ : Subgroup ↥Y) = Subgroup.normalClosure (Bb : Set ↥Y) ⊔ S.subgroupOf Y) :
    P.subgroupOf Y ≤ Subgroup.centralizer
      (Subgroup.normalClosure (Bb : Set ↥Y) : Set ↥Y) := by
  rw [Subgroup.le_centralizer_iff]
  have hN : Subgroup.normalClosure (Bb : Set ↥Y) =
      Subgroup.closure (Group.conjugatesOfSet (Bb : Set ↥Y)) := rfl
  rw [hN]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  obtain ⟨a, ha, hconj⟩ := hx
  rw [isConj_iff] at hconj
  obtain ⟨g, rfl⟩ := hconj
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro p hp
  have hg : g ∈ (⊤ : Subgroup ↥Y) := Subgroup.mem_top g
  rw [htop] at hg
  obtain ⟨n, hn, s, hs, hns⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  have hn' : s⁻¹ * n * s ∈ Subgroup.normalClosure (Bb : Set ↥Y) :=
    (inferInstance : (Subgroup.normalClosure (Bb : Set ↥Y)).Normal).conj_mem n hn s⁻¹
  have hb : (s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹ ∈ Bb :=
    (Subgroup.mem_normalizer_iff.mp (hNnorm hn') a).mp ha
  have hsS : (s : MulAut V) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have hpP : (p : MulAut V) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hsp : s⁻¹ * p * s ∈ P.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hSP (S.inv_mem hsS)) (p : MulAut V)).mp hpP
  have hcommb : (s⁻¹ * p * s) * ((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹) =
      ((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹) * (s⁻¹ * p * s) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommY hb) (s⁻¹ * p * s) hsp
  have hx' : g * a * g⁻¹ = s * ((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹) * s⁻¹ := by
    rw [← hns]
    group
  rw [hx']
  calc p * (s * ((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹) * s⁻¹)
      = s * ((s⁻¹ * p * s) * ((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹)) * s⁻¹ := by
        group
    _ = s * (((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹) * (s⁻¹ * p * s)) * s⁻¹ := by
        rw [hcommb]
    _ = (s * ((s⁻¹ * n * s) * a * (s⁻¹ * n * s)⁻¹) * s⁻¹) * p := by
        group

private theorem le_normalizer_sSup_pstarSet_eoff {V : Type} [CommGroup V]
    {S : Subgroup (MulAut V)} :
    S ≤ Subgroup.normalizer (sSup (PstarSet S) : Subgroup (MulAut V)) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : ∀ g ∈ S,
      (sSup (PstarSet S)).map (MulAut.conj g).toMonoidHom ≤ sSup (PstarSet S) := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isPStar_map_conj_eoff hA hg)
  refine le_antisymm (hle s hs) ?_
  intro y hy
  have h := hle s⁻¹ (S.inv_mem hs) ⟨y, hy, rfl⟩
  refine ⟨(MulAut.conj s⁻¹).toMonoidHom y, h, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

private theorem normalClosure_le_normalizer_of_commute_eoff {V : Type} [CommGroup V]
    {Y : Subgroup (MulAut V)} {Bb : Subgroup ↥Y}
    (hcomm : ∀ g : ↥Y, Bb.map (MulAut.conj g).toMonoidHom ≠ Bb →
      ⁅Bb, Bb.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    Subgroup.normalClosure (Bb : Set ↥Y) ≤ Subgroup.normalizer (Bb : Set ↥Y) := by
  change Subgroup.closure (Group.conjugatesOfSet (Bb : Set ↥Y)) ≤ _
  refine (Subgroup.closure_le _).mpr ?_
  rintro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  obtain ⟨a, ha, hconj⟩ := hx
  rw [isConj_iff] at hconj
  obtain ⟨g, rfl⟩ := hconj
  have hconj : Bb.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Bb : Set ↥Y) := by
    by_cases hg : Bb.map (MulAut.conj g).toMonoidHom = Bb
    · rw [hg]
      exact Subgroup.le_normalizer
    · have hc := hcomm g hg
      rw [Subgroup.commutator_comm] at hc
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
        (Subgroup.centralizer_le_normalizer _)
  exact hconj (Subgroup.mem_map_of_mem _ ha)

private theorem gomiBarOf_top_decomposition_eoff {B : Subgroup Ω} (hBle : B ≤ G)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    {S : Subgroup (MulAut ↥(gomiV G))} (hS : IsSylowIn 2 S (autOn G (gomiV G))) :
    ∃ T : Subgroup Ω, IsSylowTwoOf T G ∧ autOn T (gomiV G) = S ∧
      (⊤ : Subgroup ↥(autOn G (gomiV G))) =
        Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊔
          S.subgroupOf (autOn G (gomiV G)) := by
  obtain ⟨T, hT, hTS⟩ := exists_isSylowTwoOf_autOn_eq hS
  refine ⟨T, hT, hTS, ?_⟩
  have hCGB : conjClosure B G ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨l, hl, e, he, rfl⟩
    exact G.mul_mem (G.mul_mem hl (hBle he)) (G.inv_mem hl)
  have hmap_sup : gomiBarOf G (conjClosure B G ⊔ T) =
      gomiBarOf G (conjClosure B G) ⊔ gomiBarOf G T := by
    rw [gomiBarOf_eq_map (sup_le hCGB hT.1), Subgroup.subgroupOf_sup hCGB hT.1,
      Subgroup.map_sup, ← gomiBarOf_eq_map hCGB, ← gomiBarOf_eq_map hT.1]
  have hTSsub : gomiBarOf G T = S.subgroupOf (autOn G (gomiV G)) := by
    show (autOn T (gomiV G)).subgroupOf (autOn G (gomiV G)) = _
    rw [hTS]
  have hGG : gomiBarOf G G = ⊤ := by
    show (autOn G (gomiV G)).subgroupOf (autOn G (gomiV G)) = ⊤
    exact Subgroup.subgroupOf_self _
  have hGG' : gomiBarOf G (conjClosure B G ⊔ T) = ⊤ := by
    rw [← hGB T hT, hGG]
  rw [← hGG', hmap_sup, gomiBarOf_conjClosure hBle, hTSsub]

omit [Finite Ω] in
private theorem subgroupOf_le_centralizer_gomiBar_eoff {B : Subgroup Ω}
    {S : Subgroup (MulAut ↥(gomiV G))}
    (hcomm21 : ∀ g : ↥(autOn G (gomiV G)),
      (gomiBarOf G B).map (MulAut.conj g).toMonoidHom ≠ gomiBarOf G B →
      ⁅gomiBarOf G B, (gomiBarOf G B).map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (htop : (⊤ : Subgroup ↥(autOn G (gomiV G))) =
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊔
        S.subgroupOf (autOn G (gomiV G)))
    (hcomm : ⁅autOn B (gomiV G), sSup (PstarSet S)⁆ = ⊥) :
    (sSup (PstarSet S)).subgroupOf (autOn G (gomiV G)) ≤
      Subgroup.centralizer
        (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) :
          Set ↥(autOn G (gomiV G))) := by
  have hSP := le_normalizer_sSup_pstarSet_eoff (V := ↥(gomiV G)) (S := S)
  have hNnorm := normalClosure_le_normalizer_of_commute_eoff (Bb := gomiBarOf G B) hcomm21
  have hcommY : ⁅gomiBarOf G B,
      (sSup (PstarSet S)).subgroupOf (autOn G (gomiV G))⁆ = ⊥ :=
    commutator_subgroupOf_eoff hcomm
  exact subgroupOf_le_centralizer_normalClosure_eoff hSP hcommY hNnorm htop

theorem Gomi410Cex.commutator_autOn_sSup_pstarSet_ne_bot (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    {S : Subgroup (MulAut ↥(gomiV G))} (hS : IsSylowIn 2 S (autOn G (gomiV G))) :
    ⁅autOn B (gomiV G), sSup (PstarSet S)⁆ ≠ ⊥ := by
  intro hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBle : B ≤ G := hB.le
  have h21 := gomiHyp21_gomiBarOf (G := G) hB hBt hGB hCQ
  obtain ⟨-, -, -, htop⟩ := gomiBarOf_top_decomposition_eoff hBle hGB hS
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.centralizer
      (Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) :
        Set ↥(autOn G (gomiV G)))) :=
    not_dvd_card_centralizer_of_isPGroup_quotient (p := 2)
      (h.eq_bot_of_normal_autOn hfZ hchar hmono) h21.isPGroup_quotient
  have hPleS : sSup (PstarSet S) ≤ S := sSup_le fun A hA => hA.1.1
  have hPleY : sSup (PstarSet S) ≤ autOn G (gomiV G) := hPleS.trans hS.1
  have hPleC := subgroupOf_le_centralizer_gomiBar_eoff h21.commute htop hcomm
  obtain ⟨A, hA⟩ := pstarSet_nonempty_of_isSylowIn h45 hCQ hS
  have hAoff : IsFFStarOffender S A := hA.1
  have hAne : A ≠ ⊥ := hAoff.2.1
  have hA2 : IsPGroup 2 A := isPGroup_two_of_isElemAbelian2_eoff hAoff.2.2.1
  have hAleP : A ≤ sSup (PstarSet S) := le_sSup hA
  have hAdiv : 2 ∣ Nat.card A := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
    rw [hk]
    exact dvd_pow_self 2 (by
      intro hk0
      rw [hk0, pow_zero] at hk
      exact hAne (Subgroup.eq_bot_of_card_eq A hk))
  have h2P : 2 ∣ Nat.card ((sSup (PstarSet S)).subgroupOf (autOn G (gomiV G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleY).toEquiv]
    exact hAdiv.trans (Subgroup.card_dvd_of_le hAleP)
  exact hodd (h2P.trans (Subgroup.card_dvd_of_le hPleC))

end CFSG.GroupTheory
