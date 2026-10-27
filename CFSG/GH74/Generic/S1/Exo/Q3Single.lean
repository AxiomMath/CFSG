module

public import CFSG.GH74.Generic.S1.Exo.Q3SingleCfg
public import CFSG.GH74.Generic.S1.Exo.Q3SinglePerm
public import CFSG.GH74.Generic.S1.Exo.Q3SingleM12
public import CFSG.GH74.Generic.S1.Exo.Q3SingleSz8
public import CFSG.GH74.Generic.S1.Exo.NbIvk
public import CFSG.GH74.Generic.S1.Exo.NbCenterClasses

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.L5U5
  CFSG.Assembly.LowTwoRank

namespace Q3Cfg

variable {N : Type} [Group N] [Finite N] {c y : N} {ψA ψB : Q8 →* N} (cfg : Q3Cfg N c y ψA ψB)

include cfg

theorem false_of_alt {n : ℕ} (hn : n ≤ 11) (e : N ⧸ center N ≃* alternatingGroup (Fin n)) : False := by
  let π : N →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center N)))
  have hπ : ∀ x, π x = 1 ↔ x ∈ center N := by
    intro x
    constructor
    · intro h
      have h1 : e (QuotientGroup.mk' (center N) x) = 1 := Subtype.ext h
      have h2 : QuotientGroup.mk' (center N) x = 1 := e.injective (h1.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff x).1 h2
    · intro h
      have h2 : QuotientGroup.mk' (center N) x = 1 := (QuotientGroup.eq_one_iff x).2 h
      show ((e (QuotientGroup.mk' (center N) x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1
      rw [h2, map_one]
      rfl
  have hmem : ∀ x, π x ∈ alternatingGroup (Fin n) := fun x => (e (QuotientGroup.mk' (center N) x)).2
  obtain ⟨hinj, u, v, ⟨x, rfl⟩, ⟨x', rfl⟩, hu2, hv2, hu1, hv1, huv, hcomm, huB, hvB⟩ := cfg.quot_data π hπ
  exact perm_no_two_cent_q8 (by simp; omega) (alternatingGroup (Fin n)) (alt_fix_eight hn)
    (π.comp ψB) hinj (fun g => hmem _) (hmem x) (hmem x') hu2 hv2 hu1 hv1 huv hcomm huB hvB

theorem false_of_M12
    (e : N ⧸ center N ≃* NativeSporadic.M12) : False := by
  let π : N →* Equiv.Perm (Fin 12) :=
    NativeSporadic.M12.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center N)))
  have hπ : ∀ x, π x = 1 ↔ x ∈ center N := by
    intro x
    constructor
    · intro h
      have h1 : e (QuotientGroup.mk' (center N) x) = 1 := Subtype.ext h
      have h2 : QuotientGroup.mk' (center N) x = 1 := e.injective (h1.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff x).1 h2
    · intro h
      have h2 : QuotientGroup.mk' (center N) x = 1 := (QuotientGroup.eq_one_iff x).2 h
      show ((e (QuotientGroup.mk' (center N) x) : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 1
      rw [h2, map_one]
      rfl
  have hmem : ∀ x, π x ∈ NativeSporadic.M12 := fun x => (e (QuotientGroup.mk' (center N) x)).2
  obtain ⟨hinj, u, v, ⟨x, rfl⟩, ⟨x', rfl⟩, hu2, hv2, hu1, hv1, huv, hcomm, huB, hvB⟩ := cfg.quot_data π hπ
  exact perm_no_two_cent_q8 (by simp) NativeSporadic.M12 m12_fix_eight
    (π.comp ψB) hinj (fun g => hmem _) (hmem x) (hmem x') hu2 hv2 hu1 hv1 huv hcomm huB hvB

theorem false_of_Sz8 (h : LieModel (N ⧸ center N) .twistedB2 0 2 3) : False := by
  obtain ⟨hinj, -⟩ := cfg.quot_data (QuotientGroup.mk' (center N)) (fun x => QuotientGroup.eq_one_iff x)
  exact no_q8_of_twistedB2 h ⟨(QuotientGroup.mk' (center N)).comp ψB, hinj⟩

theorem false
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) : False := by
  have hne : center N ≠ ⊥ := by
    intro hbot
    have := cfg.c_mem
    rw [hbot, Subgroup.mem_bot] at this
    exact cfg.c_ne_one this
  rcases nb_center_classes hG hF cfg.quasi cfg.hZ cfg.gen4 cfg.gh hne with
    hSL2 | ⟨n, -, hn11, hcov⟩ | ⟨-, hexp⟩ | hM12 | hSz | hS1 | ⟨F, _, _, hFodd, ⟨e⟩⟩
  · exact cfg.false_of_sl2 hSL2
  · obtain ⟨-, -, ⟨eA⟩⟩ := hcov
    exact cfg.false_of_alt hn11 eA
  · exact cfg.false_of_exponent hexp
  · obtain ⟨eM⟩ := hM12.2.2
    exact cfg.false_of_M12 eM
  · exact cfg.false_of_Sz8 hSz.2.2
  · exact cfg.false_of_sl4 hS1
  · exact cfg.false_of_sp hFodd e

end Q3Cfg

theorem nbhd3_no_common
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    {H : Type} [Group H] [Finite H] {c y : H} {JA JB : Subgroup H} (h : Nbhd3Hyp H c y JA JB) :
    ¬ ∃ N : Subgroup H, IsComponent N ∧ (∀ g ∈ JA, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N) ∧
      (∀ g ∈ JB, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ N) := by
  rintro ⟨N, hN, hA, hB⟩
  obtain ⟨ψA, hAi, hAm, hAz⟩ := h.q8A
  obtain ⟨ψB, hBi, hBm, hBz⟩ := h.q8B
  have hNA : ∀ g, ψA g ∈ N := fun g => hA _ (hAm g) (two_elt_q8 g)
  have hNB : ∀ g, ψB g ∈ N := fun g => hB _ (hBm g) (two_elt_q8 g)
  have hcN : c ∈ N := hAz ▸ hNA _
  have hyN : y ∈ N := hBz ▸ hNB _
  let ψA' : Q8 →* ↥N := ψA.codRestrict N hNA
  let ψB' : Q8 →* ↥N := ψB.codRestrict N hNB
  let c' : ↥N := ⟨c, hcN⟩
  let y' : ↥N := ⟨y, hyN⟩
  have hyn : y' ∉ center ↥N := by
    intro hyc
    have hperf : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp hN.1.1
    have hle : N ≤ centralizer ({c * y} : Set H) := by
      intro a ha
      rw [h.mem_cent_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hyc ⟨a, ha⟩)
    have hbot := h.perfect_free N hperf hle
    rw [hbot, Subgroup.mem_bot] at hcN
    exact h.c_ne_one hcN
  have cfg : Q3Cfg ↥N c' y' ψA' ψB' :=
    { quasi := hN.1
      hZ := nb_isPGroup_center_component h.core hN
      gen4 := Gen4.subgroup N h.gen4
      gh := h.gh N (center ↥N) hN.1.2.1 hN.1.2.2
      c_mem := Subgroup.mem_center_iff.2 fun g => Subtype.ext (h.c_central (g : H))
      c_ne_one := fun e => h.c_ne_one (congrArg Subtype.val e)
      y_ne_one := fun e => h.y_ne_one (congrArg Subtype.val e)
      c_ne_y := fun e => h.c_ne_y (congrArg Subtype.val e)
      zA := Subtype.ext hAz
      zB := Subtype.ext hBz
      injA := fun a b hab => hAi (congrArg Subtype.val hab)
      injB := fun a b hab => hBi (congrArg Subtype.val hab)
      comm := fun a b => Subtype.ext (h.comm _ (hAm a) _ (hBm b))
      y_nc := hyn }
  exact cfg.false hG hF

end CFSG.GH74.Generic.S1.Exo
