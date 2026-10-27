module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.AssemblyFrame
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameCondTwist
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.EvenSporadicStandard.Wong77.Module

variable {G : Type} [Group G] {t : G}

set_option maxRecDepth 100000 in
theorem exists_sylow_pullback
    [Finite G] [IsSimpleGroup G] (M : Model G t) (hF : SquareFacts)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2) {T₀ : Subgroup J}
    (hle : T₀ ≤ Subgroup.centralizer {d}) (hcard : Nat.card T₀ = 2 ^ 18) :
    ∃ T : Sylow 2 G, ∀ x : G, x ∈ T ↔
      ∃ s : centralizer ({t} : Set G), M.ψ s ∈ T₀ ∧ (s : G) = x := by
  have hex : ∀ y ∈ T₀, ∃ x, M.ψ x = y := fun y hy => by
    have h1 := mem_centralizer_singleton_iff.1 (hle hy)
    exact (M.range y).1 h1
  have hmap : (T₀.comap M.ψ).map M.ψ = T₀ := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx⟩ := hex y hy
      refine ⟨x, ?_, hx⟩
      show M.ψ x ∈ T₀
      rw [hx]
      exact hy
  have hS'card : Nat.card (T₀.comap M.ψ) = 2 ^ 18 := by
    have h : Nat.card ((T₀.comap M.ψ).map M.ψ) = Nat.card (T₀.comap M.ψ) :=
      Subgroup.card_map_of_injective M.inj
    rw [hmap, hcard] at h
    exact h.symm
  have hLcard : Nat.card (centralizer ({t} : Set G)) = 129123503308800 := by
    have h1 : Nat.card (centralizer ({t} : Set G)) =
        Nat.card (Subgroup.centralizer ({d} : Set J)) := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x => (⟨M.ψ x, mem_Cd.2 (psi_comm_d M x)⟩ : Cd)) ⟨?_, ?_⟩)
      · intro a b h
        exact M.inj (congrArg Subtype.val h)
      · rintro ⟨c, hc⟩
        obtain ⟨x, hx⟩ := (M.range c).1 (mem_Cd.1 hc)
        exact ⟨x, Subtype.ext hx⟩
    rw [h1, card_centralizer_d]
  have hidx : ¬ 2 ∣ (T₀.comap M.ψ).index := by
    have h := Subgroup.card_mul_index (T₀.comap M.ψ)
    rw [hS'card, hLcard] at h
    have h' : 2 ^ 18 * (T₀.comap M.ψ).index = 2 ^ 18 * 492567075 := by rw [h]; norm_num
    have := Nat.eq_of_mul_eq_mul_left (by norm_num) h'
    rw [this]
    norm_num
  have hpg : IsPGroup 2 (T₀.comap M.ψ) := IsPGroup.of_card hS'card
  refine ⟨((hpg.toSylow hidx).2.map (centralizer ({t} : Set G)).subtype).toSylow
    (index_map_odd M hF hnonab ht _), fun x => ?_⟩
  show x ∈ (((hpg.toSylow hidx : Sylow 2 (centralizer ({t} : Set G))) :
    Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype) ↔ _
  rw [IsPGroup.toSylow_coe]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩

set_option maxRecDepth 100000 in
theorem exists_sylow_frame
    [Finite G] [IsSimpleGroup G] (M : Model G t) (hF : SquareFacts)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2) (hFrame : FrameFact) :
    ∃ (T : Sylow 2 G) (F : GoodFrame G),
      (T : Set G) ∩ {g : G | IsConj t g} = Set.range F.pt := by
  obtain ⟨ε, hε⟩ := Dt_eq_starSet M hF hnonab ht
  obtain ⟨φ, T₀, hker, h0, hD, hle, hcard, hT⟩ := hFrame
  have hmemT : ∀ i, φ (eVec i) ∈ T₀ := fun i => (hT _ (hD i)).2 ⟨i, rfl⟩
  have hrangeT := φ_mem_of_eVec φ hmemT
  have hrange : ∀ w : Word, ∃ x, M.ψ x = φ (Multiplicative.ofAdd w) := fun w => by
    have h1 := mem_centralizer_singleton_iff.1 (hle (hrangeT w))
    exact (M.range _).1 h1
  obtain ⟨φL, hpsiL, hkerL⟩ : ∃ φL : Multiplicative Word →* centralizer ({t} : Set G),
      (∀ w, M.ψ (φL (Multiplicative.ofAdd w)) = φ (Multiplicative.ofAdd w)) ∧
      (∀ w, φL (Multiplicative.ofAdd w) = 1 ↔ φ (Multiplicative.ofAdd w) = 1) :=
    ⟨liftHom M.ψ M.inj φ hrange, psi_liftHom M.ψ M.inj φ hrange,
      liftHom_eq_one_iff M.ψ M.inj φ hrange⟩
  obtain ⟨T, hTmem⟩ := exists_sylow_pullback M hF hnonab ht hle hcard
  let φG : Multiplicative Word →* G := (centralizer ({t} : Set G)).subtype.comp φL
  have hkerG : ∀ w : Word, φG (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode := fun w => by
    show ((φL (Multiplicative.ofAdd w) : centralizer ({t} : Set G)) : G) = 1 ↔ _
    rw [OneMemClass.coe_eq_one, hkerL, hker]
  let Fg : GoodFrame G := goodFrame_of_ker_eq φG hkerG
  have hpt : ∀ i, Fg.pt i = ((φL (eVec i) : centralizer ({t} : Set G)) : G) := fun i => rfl
  have hpsi : ∀ i, M.ψ (φL (eVec i)) = φ (eVec i) := fun i => hpsiL (Pi.single i 1)
  have htL : ∀ s : centralizer ({t} : Set G), (s : G) = t → s = φL (eVec 0) := fun s hs =>
    M.inj (by
      rw [hpsi, h0, ← M.map_t]
      congr 1
      exact Subtype.ext hs)
  have hpt0 : Fg.pt 0 = t := by
    rw [hpt]
    exact congrArg Subtype.val (htL ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ rfl).symm
  have hptT : ∀ i, Fg.pt i ∈ T := fun i =>
    (hTmem _).2 ⟨φL (eVec i), by rw [hpsi]; exact hmemT i, (hpt i).symm⟩
  cases ε
  · refine ⟨T, Fg, ?_⟩
    ext x
    constructor
    · rintro ⟨hxT, hxD⟩
      obtain ⟨s, hsT, rfl⟩ := (hTmem x).1 hxT
      by_cases hst : (s : G) = t
      · exact ⟨0, by rw [hpt0, hst]⟩
      · have h1 := (hε s).1 ⟨hxD, hst⟩
        rw [mem_starSet_false] at h1
        obtain ⟨i, -, hi⟩ := (frame_star_iff hker h0 hD hle hT (M.ψ s)).1 ⟨hsT, h1⟩
        refine ⟨i, ?_⟩
        have : φL (eVec i) = s := M.inj (by rw [hpsi, hi])
        rw [hpt, this]
    · rintro ⟨i, rfl⟩
      refine ⟨hptT i, ?_⟩
      by_cases hi : i = 0
      · rw [hi, hpt0]
        exact IsConj.refl t
      · have h1 := ((frame_star_iff hker h0 hD hle hT (φ (eVec i))).2 ⟨i, hi, rfl⟩).2
        have hs : φL (eVec i) ∈ Dt t := (hε _).2 (by
          rw [hpsi, mem_starSet_false]
          exact h1)
        rw [hpt]
        exact hs.1
  · refine ⟨T, Fg.twist, ?_⟩
    have hd : d ∈ T₀ := h0 ▸ hmemT 0
    ext x
    constructor
    · rintro ⟨hxT, hxD⟩
      obtain ⟨s, hsT, rfl⟩ := (hTmem x).1 hxT
      by_cases hst : (s : G) = t
      · exact ⟨0, by rw [Fg.twist_pt_zero, hpt0, hst]⟩
      · have h1 := (hε s).1 ⟨hxD, hst⟩
        obtain ⟨i, hi, hi'⟩ := (frame_star2_iff hker h0 hD hle hT (M.ψ s)).1 ⟨hsT, h1⟩
        refine ⟨i, ?_⟩
        have : φL (eVec 0) * φL (eVec i) = s := M.inj (by
          rw [map_mul, hpsi, hpsi, h0, hi'])
        rw [Fg.twist_pt_ne hi, hpt, hpt, ← this]
        rfl
    · rintro ⟨i, rfl⟩
      by_cases hi : i = 0
      · rw [hi, Fg.twist_pt_zero]
        exact ⟨hptT 0, by rw [hpt0]; exact IsConj.refl t⟩
      · rw [Fg.twist_pt_ne hi]
        have h1 := (frame_star2_iff hker h0 hD hle hT (d * φ (eVec i))).2 ⟨i, hi, rfl⟩
        have hmul : M.ψ (φL (eVec 0) * φL (eVec i)) = d * φ (eVec i) := by
          rw [map_mul, hpsi, hpsi, h0]
        refine ⟨(hTmem _).2 ⟨φL (eVec 0) * φL (eVec i), by rw [hmul]; exact h1.1, rfl⟩, ?_⟩
        have hs : φL (eVec 0) * φL (eVec i) ∈ Dt t := (hε _).2 (by rw [hmul]; exact h1.2)
        rw [hpt, hpt]
        exact hs.1

end CFSG.EvenSporadicStandard.TwoFi22
