module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5Z35
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Defs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5

open Subgroup CFSG.SignalizerFunctorTheorem.McBride

private lemma centralizer_conj' {G : Type*} [Group G] (c x : G) :
    Subgroup.centralizer ({c * x * c⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hg
    refine ⟨c⁻¹ * g * c, ?_, by group⟩
    calc c⁻¹ * g * c * x = c⁻¹ * (g * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * g) * c := by rw [hg]
      _ = x * (c⁻¹ * g * c) := by group
  · rintro ⟨h, hh, rfl⟩
    calc c * h * c⁻¹ * (c * x * c⁻¹) = c * (h * x) * c⁻¹ := by group
      _ = c * (x * h) * c⁻¹ := by rw [hh]
      _ = c * x * c⁻¹ * (c * h * c⁻¹) := by group

structure Setting (Y : Type*) [Group Y] (P : Subgroup Y) : Prop where
  abelian_normal : ∀ A : Subgroup Y, A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A = ⊥
  comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  cube : ∀ a ∈ P, a ^ 3 = 1
  card : Nat.card P = 9
  cent : ∀ a ∈ P, a ≠ 1 → Nonempty (↥(centralizer ({a} : Set Y)) ≃* Z35)

namespace Setting

variable {Y : Type*} [Group Y] [Finite Y] {P : Subgroup Y}

theorem isElemAbelian (h : Setting Y P) : CFSG.Open.IsElemAbelian 3 P :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (h.comm a a.2 b b.2), h.cube⟩

theorem card_centralizer (h : Setting Y P) {a : Y} (ha : a ∈ P) (ha1 : a ≠ 1) :
    Nat.card (centralizer ({a} : Set Y)) = 360 := by
  obtain ⟨e⟩ := h.cent a ha ha1
  rw [Nat.card_congr e.toEquiv, card_z35]

theorem not_dvd (h : Setting Y P) : ¬ 3 ^ 3 ∣ Nat.card Y := by
  intro h27
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card P = 3 ^ 2 := by rw [h.card]; norm_num
  have h27' : 3 ^ (2 + 1) ∣ Nat.card Y := by simpa using h27
  obtain ⟨T, hTcard, hPT⟩ :=
    Sylow.exists_subgroup_card_pow_succ (p := 3) (n := 2) (H := P) h27' hP
  have hTcard' : Nat.card T = 27 := by rw [hTcard]; norm_num
  let P' : Subgroup ↥T := P.subgroupOf T
  have hcardP' : Nat.card P' = 9 := by
    dsimp only [P']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT).toEquiv, h.card]
  have hidx : P'.index = 3 := by
    rw [Subgroup.index_eq_card_div, hcardP', hTcard']
  have hmin : Nat.minFac 27 = 3 :=
    Nat.prime_eq_prime_of_dvd_pow (p := Nat.minFac 27) (q := 3) (m := 3)
      (Nat.minFac_prime (by norm_num)) Nat.prime_three (by simpa using Nat.minFac_dvd 27)
  have hnorm : P'.Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hTcard', hmin])
  have hpg : IsPGroup 3 ↥T := IsPGroup.of_card (n := 3) (by rw [hTcard']; norm_num)
  haveI : Group.IsNilpotent ↥T := hpg.isNilpotent
  have hne : P' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardP'
    norm_num at hcardP'
  haveI : P'.Normal := hnorm
  have hinf : P' ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  have haP' : (a : ↥T) ∈ P' := a.2.1
  have hacenter : (a : ↥T) ∈ Subgroup.center ↥T := a.2.2
  have haP : ((a : ↥T) : Y) ∈ P := Subgroup.mem_subgroupOf.mp haP'
  have haY1 : ((a : ↥T) : Y) ≠ 1 := by
    intro h1
    exact ha1 (Subtype.ext (Subtype.ext (by simpa using h1)))
  have hTle : T ≤ Subgroup.centralizer ({((a : ↥T) : Y)} : Set Y) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (Subgroup.mem_center_iff.mp hacenter) ⟨t, ht⟩
    simpa using congrArg Subtype.val hcomm
  have hdvd : Nat.card T ∣ Nat.card (Subgroup.centralizer ({((a : ↥T) : Y)} : Set Y)) :=
    Subgroup.card_dvd_of_le hTle
  have h360 : Nat.card (Subgroup.centralizer ({((a : ↥T) : Y)} : Set Y)) = 360 :=
    h.card_centralizer haP haY1
  rw [hTcard', h360] at hdvd
  norm_num at hdvd

theorem centralizer_equiv (h : Setting Y P) {x : Y} (hx : orderOf x = 3) :
    Nonempty (↥(centralizer ({x} : Set Y)) ≃* Z35) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Nat.card P = 3 ^ 2 := by rw [h.card]; norm_num
  have hk : ¬ 3 ^ (2 + 1) ∣ Nat.card Y := by simpa using h.not_dvd
  obtain ⟨g, hg⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.exists_conj_mem_of_card_eq_pow
      (p := 3) (k := 2) hP hk hx
  set a : Y := g * x * g⁻¹ with ha_def
  have ha : a ∈ P := by rwa [ha_def]
  have horder_a : orderOf a = 3 := by
    rw [ha_def, ← hx]
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) x
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at horder_a
    omega
  have hmap : (Subgroup.centralizer ({x} : Set Y)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({a} : Set Y) := by
    rw [ha_def]
    exact (centralizer_conj' g x).symm
  exact ⟨(Subgroup.equivMapOfInjective (Subgroup.centralizer ({x} : Set Y))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (h.cent a ha ha1).some)⟩

theorem eq_bot_of_normal_of_coprime (h : Setting Y P) {M : Subgroup Y} (hM : M.Normal)
    (hc : Nat.Coprime 3 (Nat.card M)) : M = ⊥ := by
  have hA : CFSG.Open.IsElemAbelian 3 P := h.isElemAbelian
  have hrank : 3 ^ 2 ≤ Nat.card P := by rw [h.card]; norm_num
  haveI : M.Normal := hM
  have hAX : P ≤ Subgroup.normalizer (M : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hsup : ⨆ (a : Y) (_ : a ∈ P) (_ : a ≠ 1),
      M ⊓ Subgroup.centralizer ({a} : Set Y) = M :=
    iSup_centralizer_nonidentity Nat.prime_three hA hrank hAX hc
  have hterm : ∀ a ∈ P, a ≠ 1 → M ⊓ Subgroup.centralizer ({a} : Set Y) = ⊥ := by
    intro a ha ha1
    let C : Subgroup Y := Subgroup.centralizer ({a} : Set Y)
    let e : ↥C ≃* Z35 := (h.cent a ha ha1).some
    let K : Subgroup Z35 := ((M ⊓ C).subgroupOf C).map e.toMonoidHom
    have hKnormal : K.Normal := by
      have hMsC : (M.subgroupOf C).Normal := hM.subgroupOf C
      have heq : (M ⊓ C).subgroupOf C = M.subgroupOf C := Subgroup.inf_subgroupOf_right M C
      dsimp only [K]
      rw [heq]
      exact Subgroup.Normal.map hMsC e.toMonoidHom e.surjective
    have hKcard : Nat.card K = Nat.card ↥(M ⊓ C) := by
      dsimp only [K]
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective ((M ⊓ C).subgroupOf C)
        e.toMonoidHom e.injective).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ C ≤ C)).toEquiv
    have hKcoprime : Nat.Coprime 3 (Nat.card K) := by
      rw [hKcard]
      exact hc.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : M ⊓ C ≤ M))
    have hKbot : K = ⊥ := eq_bot_of_normal_of_coprime_z35 hKnormal hKcoprime
    have hsub : (M ⊓ C).subgroupOf C = ⊥ := by
      dsimp only [K] at hKbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hKbot
    have hd : Disjoint (M ⊓ C) C := Subgroup.subgroupOf_eq_bot.mp hsub
    have hd' : M ⊓ C = ⊥ := hd.eq_bot_of_le inf_le_right
    dsimp only [C] at hd'
    exact hd'
  have hle : M ≤ ⊥ := by
    rw [← hsup]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    exact le_of_eq (hterm a ha ha1)
  exact le_bot_iff.mp hle

theorem solvableRadical_eq_bot (h : Setting Y P) : CFSG.solvableRadical Y = ⊥ := by
  rw [CFSG.solvableRadical]
  refine le_bot_iff.mp (sSup_le fun N hN => le_bot_iff.mpr ?_)
  by_contra hNbot
  classical
  obtain ⟨m, hm⟩ := hN.2.solvable
  have hex : ∃ k : ℕ, derivedSeries ↥N k = ⊥ := ⟨m, hm⟩
  let n := Nat.find hex
  have hn : derivedSeries ↥N n = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    have htop : (⊤ : Subgroup ↥N) = ⊥ := by
      have h' := hn
      rw [h0, derivedSeries_zero] at h'
      exact h'
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    exact hx1 ((Subgroup.eq_bot_iff_forall (⊤ : Subgroup ↥N)).mp htop ⟨x, hx⟩ trivial)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  let k := n - 1
  have hk_lt : k < n := by omega
  have hk_ne : derivedSeries ↥N k ≠ ⊥ := Nat.find_min hex hk_lt
  have hk_succ : derivedSeries ↥N (k + 1) = ⊥ := by
    have hk1 : k + 1 = n := by omega
    rw [hk1]
    exact hn
  haveI : N.Normal := hN.1
  let D : Subgroup Y := (derivedSeries ↥N k).map N.subtype
  have hDne : D ≠ ⊥ := by
    intro hbot
    dsimp only [D] at hbot
    exact hk_ne ((Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hbot)
  have hDnormal : D.Normal := by
    dsimp only [D]
    exact inferInstance
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    have hcommL : IsMulCommutative ↥(derivedSeries ↥N k) := by
      rw [← Subgroup.commutator_self_eq_bot_iff]
      rw [← derivedSeries_succ (G := ↥N) k, hk_succ]
    intro a ha b hb
    dsimp only [D] at ha hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hh := hcommL.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
    simpa using congrArg (fun x : ↥(derivedSeries ↥N k) => (N.subtype (x : ↥N))) hh
  exact hDne (h.abelian_normal D hDnormal hDcomm)

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5
