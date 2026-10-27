module

public import CFSG.GH74.Generic.BProg.B3.Obs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

open CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification

namespace ObsPump

variable {G : Type} [Group G] [Finite G]

section Coprime

variable {u : G} {J : Subgroup G}

def qSub (S A : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ S ∧ ∀ b ∈ A, b * g * b⁻¹ ∈ S}
  one_mem' := ⟨S.one_mem, fun b _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxA⟩ ⟨hy, hyA⟩
    refine ⟨S.mul_mem hx hy, fun b hb => ?_⟩
    have : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
    rw [this]
    exact S.mul_mem (hxA b hb) (hyA b hb)
  inv_mem' := by
    rintro x ⟨hx, hxA⟩
    refine ⟨S.inv_mem hx, fun b hb => ?_⟩
    have : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
    rw [this]
    exact S.inv_mem (hxA b hb)

end Coprime

end ObsPump

section LocBal

variable {X : Type} [Group X] [Finite X]

namespace ObsPump

omit [Finite X] in
theorem rhoL_eq_one_iff {L : Subgroup X} (hL : IsComponent L) (m : ↥(normalizer (L : Set X))) :
    rhoL L m = 1 ↔ ∀ x ∈ L, (m : X) * x = x * (m : X) := by
  have : Group.IsPerfect L := hL.1.1
  have hker : (rhoL L).ker = (Subgroup.centralizer (L : Set X)).subgroupOf (normalizer (L : Set X)) :=
    CFSG.LocalAnalysis.ComponentInitial.ker_centerQuotient_comp_normalizerConjHom L
  have h1 : rhoL L m = 1 ↔ m ∈ (rhoL L).ker := MonoidHom.mem_ker.symm
  rw [h1, hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  exact ⟨fun h x hx => (h x hx).symm, fun h x hx => (h x hx).symm⟩

end ObsPump

theorem not_locBal32_of_delta (_hO : CFSG.pPrimeCore 2 X = ⊥)
    {L : Subgroup X} (hL : IsComponent L) {B F N : Subgroup X} (hBL : B ≤ normalizer (L : Set X))
    (hB2 : ∀ b ∈ B, b * b = 1) (hFB : F ≤ B) (hF4 : Nat.card ↥F = 4)
    (hFfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ l ∈ L, f * l = l * f) (hNL : N ≤ normalizer (L : Set X))
    (hNF : N ≤ deltaCore F) (hNc : ¬ ∀ n ∈ N, ∀ l ∈ L, n * l = l * n) :
    ¬ IsLocBal32 (↥L ⧸ center ↥L) ((B.subgroupOf (normalizer (L : Set X))).map (rhoL L)) := by
  intro hbal
  set M : Subgroup X := normalizer (L : Set X) with hM
  have hFM : F ≤ M := fun f hf => hBL (hFB hf)
  have hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      (rhoL L).range := CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp L
  let φ : M →* (rhoL L).range := (rhoL L).rangeRestrict
  have hφker : φ.ker = (rhoL L).ker := MonoidHom.ker_rangeRestrict (rhoL L)
  have hφval : ∀ m : M, ((φ m : (rhoL L).range) : MulAut (L ⧸ Subgroup.center L)) = rhoL L m :=
    fun m => rfl
  set F' : Subgroup M := F.subgroupOf M with hF'
  have hFinj : ∀ m ∈ F', φ m = 1 → m = 1 := by
    intro m hm hm1
    have h1 : rhoL L m = 1 := by
      have := congrArg Subtype.val hm1
      rw [hφval] at this
      exact this
    have h2 := (ObsPump.rhoL_eq_one_iff hL m).mp h1
    by_contra hne
    exact hFfaith (m : X) ((Subgroup.mem_subgroupOf).mp hm) (fun h => hne (Subtype.ext h))
      h2
  have hcard : Nat.card (F'.map φ) = 4 := by
    have hbij : Function.Bijective (φ.subgroupMap F') := by
      refine ⟨?_, φ.subgroupMap_surjective F'⟩
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro m hm
      exact Subtype.ext (hFinj m m.2 (by
        have h2 := MonoidHom.mem_ker.mp hm
        exact congrArg Subtype.val h2))
    have hc : Nat.card (F'.map φ) = Nat.card F := by
      rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
    rw [hc]
    exact hF4
  have hexp : ∀ g ∈ F'.map φ, g * g = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hB2 m (hFB ((Subgroup.mem_subgroupOf).mp hm)))
    rw [this, map_one]
  have hB'le : (B.subgroupOf M).map (rhoL L) ≤ (rhoL L).range := fun x hx => by
    obtain ⟨m, -, rfl⟩ := hx
    exact ⟨m, rfl⟩
  have hD'le : F'.map φ ≤ ((B.subgroupOf M).map (rhoL L)).subgroupOf (rhoL L).range := by
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨m, Subgroup.mem_subgroupOf.mpr
      (hFB ((Subgroup.mem_subgroupOf).mp hm)), rfl⟩
  have hdelta : deltaCore (F'.map φ) = ⊥ :=
    (hbal (rhoL L).range hInn hB'le).2 _ hD'le hcard hexp
  have hNle : (N.subgroupOf M).map φ ≤ deltaCore (F'.map φ) := by
    refine le_deltaCore fun g hg hg1 => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    have hmF : (m : X) ∈ F := (Subgroup.mem_subgroupOf).mp hm
    have hm1 : (m : X) ≠ 1 := by
      intro h
      have hm1' : m = 1 := Subtype.ext h
      exact hg1 (by rw [hm1']; exact map_one φ)
    have hNm : N.subgroupOf M ≤ CFSG.Assembly.Dichotomy.involutionOddCore m := fun u hu =>
      LocalBalance.subgroupOf_involutionOddCore_le m
        ((Subgroup.mem_subgroupOf).mpr
          (deltaCore_le_involutionOddCore hmF hm1 (hNF ((Subgroup.mem_subgroupOf).mp hu))))
    exact (Subgroup.map_mono hNm).trans
      (map_involutionOddCore_le φ (MonoidHom.rangeRestrict_surjective _)
        (isPGroup_zpowers_of_mul_self_eq_one
          (Subtype.ext (hB2 (m : X) (hFB hmF)) : m * m = 1)))
  rw [hdelta] at hNle
  apply hNc
  intro n hn x hx
  have hmem : φ ⟨n, hNL hn⟩ ∈ (⊥ : Subgroup ((rhoL L).range)) :=
    hNle ⟨⟨n, hNL hn⟩, (Subgroup.mem_subgroupOf).mpr hn, rfl⟩
  have h1 : rhoL L ⟨n, hNL hn⟩ = 1 := by
    have := congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    rw [hφval] at this
    exact this
  exact (ObsPump.rhoL_eq_one_iff hL ⟨n, hNL hn⟩).mp h1 x hx

theorem not_locBal32_of_delta_weak (_hO : CFSG.pPrimeCore 2 X = ⊥)
    {L : Subgroup X} (hL : IsComponent L) {B : Subgroup X} (hBL : B ≤ normalizer (L : Set X))
    {f n e : X} (hfB : f ∈ B) (hf2 : f * f = 1) (heB : e ∈ B)
    (hfL : ¬ ∀ l ∈ L, f * l = l * f) (hnL : n ∈ normalizer (L : Set X))
    (hn : n ∈ CFSG.Assembly.Dichotomy.involutionOddCore f)
    (hne : ¬ ∀ l ∈ L, ⁅n, e⁆ * l = l * ⁅n, e⁆) :
    ¬ IsLocBal32 (↥L ⧸ center ↥L) ((B.subgroupOf (normalizer (L : Set X))).map (rhoL L)) := by
  intro hbal
  set M : Subgroup X := normalizer (L : Set X) with hM
  have hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      (rhoL L).range := CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp L
  let φ : M →* (rhoL L).range := (rhoL L).rangeRestrict
  have hφval : ∀ m : M, ((φ m : (rhoL L).range) : MulAut (L ⧸ Subgroup.center L)) = rhoL L m :=
    fun m => rfl
  have hB'le : (B.subgroupOf M).map (rhoL L) ≤ (rhoL L).range := fun x hx => by
    obtain ⟨m, -, rfl⟩ := hx
    exact ⟨m, rfl⟩
  have hfM : f ∈ M := hBL hfB
  have heM : e ∈ M := hBL heB
  have hb1 : φ ⟨f, hfM⟩ ≠ 1 := by
    intro h
    apply hfL
    have h1 : rhoL L ⟨f, hfM⟩ = 1 := by
      have := congrArg Subtype.val h
      rw [hφval] at this
      exact this
    exact (ObsPump.rhoL_eq_one_iff hL ⟨f, hfM⟩).mp h1
  have hcore : φ ⟨n, hnL⟩ ∈ CFSG.Assembly.Dichotomy.involutionOddCore (φ ⟨f, hfM⟩) := by
    have h1 : (⟨n, hnL⟩ : M) ∈ CFSG.Assembly.Dichotomy.involutionOddCore (⟨f, hfM⟩ : M) :=
      LocalBalance.subgroupOf_involutionOddCore_le ⟨f, hfM⟩ (Subgroup.mem_subgroupOf.mpr hn)
    exact map_involutionOddCore_le φ (MonoidHom.rangeRestrict_surjective _)
      (isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hf2 : (⟨f, hfM⟩ : M) * ⟨f, hfM⟩ = 1))
      (Subgroup.mem_map_of_mem φ h1)
  have hbB : φ ⟨f, hfM⟩ ∈ ((B.subgroupOf M).map (rhoL L)).subgroupOf (rhoL L).range :=
    Subgroup.mem_subgroupOf.mpr ⟨⟨f, hfM⟩, Subgroup.mem_subgroupOf.mpr hfB, rfl⟩
  have heB' : φ ⟨e, heM⟩ ∈ ((B.subgroupOf M).map (rhoL L)).subgroupOf (rhoL L).range :=
    Subgroup.mem_subgroupOf.mpr ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.mpr heB, rfl⟩
  have key := (hbal (rhoL L).range hInn hB'le).1 _ hbB hb1 _ hcore _ heB'
  apply hne
  have hcM : ⁅n, e⁆ ∈ M := by
    simp only [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hnL heM) (M.inv_mem hnL)) (M.inv_mem heM)
  have hcomm : ⁅(⟨n, hnL⟩ : M), (⟨e, heM⟩ : M)⁆ = ⟨⁅n, e⁆, hcM⟩ := rfl
  rw [← map_commutatorElement, hcomm] at key
  have h1 : rhoL L ⟨⁅n, e⁆, hcM⟩ = 1 := by
    have := congrArg Subtype.val key
    rw [hφval] at this
    exact this
  intro l hl
  exact (ObsPump.rhoL_eq_one_iff hL ⟨⁅n, e⁆, hcM⟩).mp h1 l hl

end LocBal

section Bridge

variable {G : Type} [Group G] [Finite G]

namespace ObsPump

omit [Finite G] in
theorem bar_mem_normalizer {a x : G} {J : Subgroup G} (hJa : J ≤ centralizer ({a} : Set G))
    (hx : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G)) :
    barMk ↥(centralizer ({a} : Set G)) ⟨x, hx⟩ ∈
      normalizer ((PumpCalc.bar a J : Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set _) := by
  have h2 : (⟨x, hx⟩ : ↥(centralizer ({a} : Set G))) ∈
      normalizer ((J.subgroupOf (centralizer ({a} : Set G)) : Subgroup _) : Set _) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJa]
    exact hxJ
  exact Subgroup.le_normalizer_map _ ⟨_, h2, rfl⟩

theorem mem_cSec_of_bar_comm {a q : G} {J : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hq : q ∈ centralizer ({a} : Set G))
    (h : ∀ l ∈ PumpCalc.bar a J, barMk ↥(centralizer ({a} : Set G)) ⟨q, hq⟩ * l =
      l * barMk ↥(centralizer ({a} : Set G)) ⟨q, hq⟩) :
    q ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  refine TwoThin.mem_centralizerSection_of_map_eq hJ.1 (isPCompIn_two_iff.mp hJ).2 hq fun m hm => ?_
  have h1 := h (barMk ↥(centralizer ({a} : Set G)) m) ⟨m, hm, rfl⟩
  rw [map_mul, map_mul, map_inv]
  generalize barMk ↥(centralizer ({a} : Set G)) m = y at h1 ⊢
  generalize barMk ↥(centralizer ({a} : Set G)) ⟨q, hq⟩ = z at h1 ⊢
  calc z * y * z⁻¹ = (y * z) * z⁻¹ := by rw [h1]
    _ = y := by group

end ObsPump

theorem Obs32.not_locBal32_rank2 {A D J : Subgroup G} {a : G} (h : Obs32 A a D J)
    (hD2 : pRank 2 ↥D = 2) :
    ¬ IsLocBal32 (↥(PumpCalc.bar a J) ⧸ center ↥(PumpCalc.bar a J))
      (((PumpCalc.bar a D).subgroupOf
        (normalizer ((PumpCalc.bar a J : Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set _))).map
          (rhoL (PumpCalc.bar a J))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDA, hDel, hDrk⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hDcard : Nat.card ↥D = 4 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel, hD2]
    norm_num
  set Y : Subgroup G := centralizer ({a} : Set G) with hY
  have hDY : ∀ d ∈ D, d ∈ Y := fun d hd =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.y_cent d (hDA hd))
  have hJY : J ≤ Y := h.comp.1
  have hDH : D ≤ Y := hDY
  have hdel : ((AG D).subgroupOf Y).map (barMk ↥Y) ≤
      deltaCore ((D.subgroupOf Y).map (barMk ↥Y)) :=
    Th2.Bal.map_le_deltaCore (a := a) hDsq fun d hd hd1 => iInf₂_le d ⟨hd, hd1⟩
  have hnle : ¬ AG D ⊓ centralizer ({a} : Set G) ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
    rcases h.unbal with ⟨-, hnle⟩ | ⟨hD1, -⟩
    · exact hnle
    · omega
  refine not_locBal32_of_delta (CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _)
    (PumpCalc.isComponent_bar h.comp) (B := PumpCalc.bar a D) (F := PumpCalc.bar a D)
    (N := ((AG D).subgroupOf Y).map (barMk ↥Y)) ?_ ?_ le_rfl ?_ ?_ ?_ hdel ?_
  · rintro _ ⟨d₀, hd₀, rfl⟩
    exact ObsPump.bar_mem_normalizer hJY d₀.2 (h.D_norm (Subgroup.mem_subgroupOf.mp hd₀))
  · rintro _ ⟨d₀, hd₀, rfl⟩
    rw [← map_mul]
    have : d₀ * d₀ = 1 := Subtype.ext (hDsq _ (Subgroup.mem_subgroupOf.mp hd₀))
    rw [this, map_one]
  · exact (Th2.Bal.card_map_piBar hDsq hDH).trans hDcard
  · rintro _ ⟨d₀, hd₀, rfl⟩ hf1 hcomm
    have hd1 : (d₀ : G) ≠ 1 := fun h1 => hf1 (by
      have : d₀ = 1 := Subtype.ext h1
      rw [this, map_one])
    exact h.D_faith _ (Subgroup.mem_subgroupOf.mp hd₀) hd1
      (ObsPump.mem_cSec_of_bar_comm h.comp d₀.2 hcomm)
  · rintro _ ⟨x₀, hx₀, rfl⟩
    exact ObsPump.bar_mem_normalizer hJY x₀.2
      (h.AG_inf_le_normalizer (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hx₀, x₀.2⟩))
  · intro hall
    obtain ⟨x, hx, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    have hxY : x ∈ Y := (Subgroup.mem_inf.mp hx).2
    apply hxS
    exact ObsPump.mem_cSec_of_bar_comm h.comp hxY
      (hall _ ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hx).1, rfl⟩)

theorem Obs32.not_locBal32_rank1 {A D J : Subgroup G} {a : G} (h : Obs32 A a D J)
    (hD1 : pRank 2 ↥D = 1) (hAJ : A ≤ normalizer (J : Set G)) :
    ¬ IsLocBal32 (↥(PumpCalc.bar a J) ⧸ center ↥(PumpCalc.bar a J))
      (((PumpCalc.bar a A).subgroupOf
        (normalizer ((PumpCalc.bar a J : Subgroup (barQ ↥(centralizer ({a} : Set G)))) : Set _))).map
          (rhoL (PumpCalc.bar a J))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDA, hDel, hDrk⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  set Y : Subgroup G := centralizer ({a} : Set G) with hY
  have hAY : ∀ x ∈ A, x ∈ Y := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.y_cent x hx)
  have hJY : J ≤ Y := h.comp.1
  obtain ⟨c, hc, b, hb, hcb⟩ : ∃ c ∈ AG D ⊓ centralizer ({a} : Set G), ∃ b ∈ A,
      ⁅c, b⁆ ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
    rcases h.unbal with ⟨hD2, -⟩ | ⟨-, c, hc, b, hb, hcb⟩
    · omega
    · exact ⟨c, hc, b, hb, hcb⟩
  obtain ⟨d, hdD, hd1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) hDrk
    (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
  have hcY : c ∈ Y := (Subgroup.mem_inf.mp hc).2
  have hdY : d ∈ Y := hAY d (hDA hdD)
  have hbY : b ∈ Y := hAY b hb
  have hdel : ((AG D).subgroupOf Y).map (barMk ↥Y) ≤
      deltaCore ((D.subgroupOf Y).map (barMk ↥Y)) :=
    Th2.Bal.map_le_deltaCore (a := a) hDsq fun d hd hd1 => iInf₂_le d ⟨hd, hd1⟩
  have hπd1 : barMk ↥Y ⟨d, hdY⟩ ≠ 1 := fun h1 => by
    have h2 : (⟨d, hdY⟩ : ↥Y) * ⟨d, hdY⟩ = 1 := Subtype.ext (hDsq d hdD)
    exact hd1 (congrArg Subtype.val
      (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore h2 (Th2.Bal.piBar_eq_one_iff.mp h1)))
  have hπc : barMk ↥Y ⟨c, hcY⟩ ∈ CFSG.Assembly.Dichotomy.involutionOddCore (barMk ↥Y ⟨d, hdY⟩) :=
    deltaCore_le_involutionOddCore (D := (D.subgroupOf Y).map (barMk ↥Y))
      ⟨⟨d, hdY⟩, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩ hπd1
      (hdel ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hc).1, rfl⟩)
  have hAbar : ∀ x : ↥Y, (x : G) ∈ A →
      barMk ↥Y x ∈ normalizer ((PumpCalc.bar a J : Subgroup (barQ ↥Y)) : Set _) := fun x hx =>
    ObsPump.bar_mem_normalizer hJY x.2 (hAJ hx)
  refine not_locBal32_of_delta_weak (CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _)
    (PumpCalc.isComponent_bar h.comp) (B := PumpCalc.bar a A) (f := barMk ↥Y ⟨d, hdY⟩)
    (n := barMk ↥Y ⟨c, hcY⟩) (e := barMk ↥Y ⟨b, hbY⟩) ?_ ?_ ?_ ?_ ?_ ?_ hπc ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hAbar x (Subgroup.mem_subgroupOf.mp hx)
  · exact ⟨⟨d, hdY⟩, Subgroup.mem_subgroupOf.mpr (hDA hdD), rfl⟩
  · rw [← map_mul]
    have : (⟨d, hdY⟩ : ↥Y) * ⟨d, hdY⟩ = 1 := Subtype.ext (hDsq d hdD)
    rw [this, map_one]
  · exact ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  · intro hcomm
    exact h.D_faith d hdD hd1 (ObsPump.mem_cSec_of_bar_comm h.comp hdY hcomm)
  · exact ObsPump.bar_mem_normalizer hJY hcY (h.AG_inf_le_normalizer hc)
  · intro hcomm
    apply hcb
    have hcbY : ⁅c, b⁆ ∈ Y := by
      simp only [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem hcY hbY) (Y.inv_mem hcY)) (Y.inv_mem hbY)
    refine ObsPump.mem_cSec_of_bar_comm h.comp hcbY ?_
    have e : (⟨⁅c, b⁆, hcbY⟩ : ↥Y) = ⁅(⟨c, hcY⟩ : ↥Y), (⟨b, hbY⟩ : ↥Y)⁆ := rfl
    rw [e, map_commutatorElement]
    exact hcomm

end Bridge

end CFSG.GH74.Generic.BProg.B3
