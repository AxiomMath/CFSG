module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ALe
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PerfCoreMap

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem Cover217.local_frame {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (ha : Valid217 A c L a) :
    ∃ (a' : ↥L) (I' : Subgroup ↥L), (a' : G) = a ∧ a' ∉ Subgroup.center ↥L ∧ a' ^ 3 = 1 ∧
      I' ≤ Subgroup.centralizer ({a'} : Set ↥L) ∧ Nonempty (↥I' ≃* alternatingGroup (Fin 6)) ∧
      iCore L a = I'.map L.subtype ∧
      Nat.card ↥(Subgroup.zpowers a' ⊔ Subgroup.center ↥L) = 9 ∧
      Disjoint (Subgroup.zpowers a' ⊔ Subgroup.center ↥L) I' ∧
      (∀ d ∈ Subgroup.zpowers a' ⊔ Subgroup.center ↥L,
        ∀ x ∈ Subgroup.centralizer ({a'} : Set ↥L), d * x = x * d) ∧
      Subgroup.zpowers a' ⊔ Subgroup.center ↥L ⊔ I' = Subgroup.centralizer ({a'} : Set ↥L) ∧
      NonCentral 3 (a' : ↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  have hab := h.isElemAbelian_A
  set a' : ↥L := ⟨a, hAL ha.mem⟩ with ha'
  have ha'c : a' ∉ Subgroup.center ↥L := by
    intro hmem
    rw [h.center_eq hθ] at hmem
    apply ha.not_mem
    have := Subgroup.mem_map_of_mem L.subtype hmem
    rw [MonoidHom.map_zpowers] at this
    exact this
  have ha3' : a' ^ 3 = 1 := Subtype.ext (hab.2 a ha.mem)
  have ha3 : a' ^ 3 ∈ Subgroup.center ↥L := by rw [ha3']; exact Subgroup.one_mem _
  have hNC : NonCentral 3 (a' : ↥L ⧸ Subgroup.center ↥L) := by
    obtain ⟨l, ⟨w, hw, hlw⟩, hnc⟩ := ha.proj
    have hwL : w ∈ L := by
      have : w = (l : G)⁻¹ * a := by rw [hlw]; group
      rw [this]
      exact L.mul_mem (L.inv_mem l.2) (hAL ha.mem)
    have hw' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hw x x.2)
    have hq : (a' : ↥L ⧸ Subgroup.center ↥L) = (l : ↥L ⧸ Subgroup.center ↥L) := by
      have : a' = l * ⟨w, hwL⟩ := Subtype.ext hlw
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hw', mul_one]
    rw [hq]; exact hnc
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer
      ({e (a' : ↥L ⧸ Subgroup.center ↥L)} : Set NativeSporadic.J3)) := by
    have hq3 : (a' : ↥L ⧸ Subgroup.center ↥L) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 ha3
    have hq1 : (a' : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := fun h1 =>
      ha'c ((QuotientGroup.eq_one_iff _).1 h1)
    exact five_dvd_centralizer_of_nonCentral e hq3 hq1 hNC
  obtain ⟨I', hI'C, hI'perf, hφ, hI'max, -, hD9, hDI, hDcomm, hCeq⟩ :=
    centralizer_structure_J3Cover hq hZ3 e ha'c ha3 h5
  have hC : Subgroup.centralizer ({a} : Set G) ⊓ L =
      (Subgroup.centralizer ({a'} : Set ↥L)).map L.subtype := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨hx, hxL⟩
      exact ⟨⟨x, hxL⟩, Subtype.ext hx, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨congrArg Subtype.val hx', x'.2⟩
  have hI : iCore L a = I'.map L.subtype := by
    unfold iCore
    rw [hC]
    exact CFSG.AGLEmbeddingD2.Wilson.Proving.perfCore_map_of_greatest L.subtype
      L.subtype_injective _ I' hI'C hI'perf hI'max
  exact ⟨a', I', rfl, ha'c, ha3', hI'C, hφ, hI, hD9, hDI, hDcomm, hCeq, hNC⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.exists_U0 {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hfr : Frame217 E c L a) :
    ∃ U₀ ∈ fourGroupsMinus E, U₀ ≤ iCore L a ∧
      ∀ b ∈ E ⊓ Subgroup.centralizer (U₀ : Set G),
        b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
  have hEA : E ≤ A := h.pair.mem_E.2
  have ha := hfr.valid hEA
  obtain ⟨a', I', ha'G, ha'c, ha3, hI'C, ⟨φ⟩, hI, hD9, hDI, hDcomm, hCeq, -⟩ :=
    h.local_frame hθ hAL ha
  have hab := h.isElemAbelian_A
  have hab' := isElemAbelian_iff.1 hab
  have hcE : c ∈ E := (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1
  have hE27 : Nat.card E = 27 := h.pair.mem_E.1.2.1
  have hEL : E ≤ L := hEA.trans hAL
  set D : Subgroup ↥L := Subgroup.zpowers a' ⊔ Subgroup.center ↥L with hD
  set EX : Subgroup ↥L := E.subgroupOf L with hEX
  have hEXmem : ∀ x : ↥L, x ∈ EX ↔ (x : G) ∈ E := fun x => Subgroup.mem_subgroupOf
  have hEXcard : Nat.card EX = 27 := by
    rw [hEX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE27]
  have hcenter : Subgroup.center ↥L ≤ EX := by
    rw [h.center_eq hθ, Subgroup.zpowers_le]
    exact (hEXmem _).2 hcE
  have ha'EX : a' ∈ EX := (hEXmem a').2 (by rw [ha'G]; exact hfr.mem)
  have hDEX : D ≤ EX := sup_le (Subgroup.zpowers_le.2 ha'EX) hcenter
  have hEXcomm : ∀ x ∈ EX, ∀ y ∈ EX, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hab'.1 _ (hEA ((hEXmem x).1 hx)) _ (hEA ((hEXmem y).1 hy)))
  have hEXC : EX ≤ Subgroup.centralizer ({a'} : Set ↥L) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hEXcomm x hx a' ha'EX)
  obtain ⟨e₀, he₀, he₀D⟩ : ∃ e₀ ∈ EX, e₀ ∉ D := by
    by_contra hno
    push Not at hno
    have : Nat.card EX ≤ Nat.card D := Subgroup.card_le_of_le (fun x hx => hno x hx)
    omega
  have he₀C : e₀ ∈ D ⊔ I' := by rw [hCeq]; exact hEXC he₀
  obtain ⟨d, hd, i, hi, hdi⟩ := (mem_sup_of_commute
    (fun x hx y hy => hDcomm x hx y (hI'C hy))).1 he₀C
  have hiEX : i ∈ EX := by
    have : i = d⁻¹ * e₀ := by rw [← hdi]; group
    rw [this]
    exact mul_mem (inv_mem (hDEX hd)) he₀
  have hi1 : i ≠ 1 := by
    intro h1
    apply he₀D
    rw [← hdi, h1, mul_one]
    exact hd
  have hi3 : i ^ 3 = 1 := Subtype.ext (hab'.2 (i : G) (hEA ((hEXmem i).1 hiEX)))
  have hiD : i ∉ D := fun hiD => hi1 (Subgroup.disjoint_def.1 hDI hiD hi)
  obtain ⟨u, v, huI, hvI, huv, huu, hvv, hyu, hyv, hu1, hv1, hne⟩ :=
    exists_V4_data I' φ hi hi3 hi1
  obtain ⟨W, hWeq, -, hW2, hWcomm, hWN⟩ := V4_aux i u v hi3 huv huu hvv hyu hyv hu1
  have hWcard : Nat.card W = 4 := hWeq ▸ card_closure_pair_of_involutions u v huv huu hvv hu1 hv1 hne
  have hWI : W ≤ I' := by
    rw [hWeq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact huI
    · exact hvI
  have hord : orderOf i = 3 := orderOf_eq_prime hi3 hi1
  have hdisj : Disjoint D (Subgroup.zpowers i) := by
    rw [Subgroup.disjoint_def]
    intro x hxD hxi
    rcases mem_zpowers_of_pow_three hi3 hxi with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hxD) hiD
    · exfalso
      apply hiD
      have : i = (i ^ 2) ^ 2 := by
        have : (i ^ 2) ^ 2 = i ^ 3 * i := by group
        rw [this, hi3, one_mul]
      rw [this]
      exact pow_mem (h1 ▸ hxD) 2
  have hsup27 : 27 ≤ Nat.card ↥(D ⊔ Subgroup.zpowers i) := by
    have := card_mul_le_card_sup_of_disjoint D (Subgroup.zpowers i) hdisj
    rw [hD9, Nat.card_zpowers, hord] at this
    omega
  have hDiEX : D ⊔ Subgroup.zpowers i ≤ EX := sup_le hDEX (Subgroup.zpowers_le.2 hiEX)
  have hEXeq : EX = D ⊔ Subgroup.zpowers i :=
    (Subgroup.eq_of_le_of_card_ge hDiEX (by rw [hEXcard]; exact hsup27)).symm
  have hDW : D ≤ Subgroup.normalizer (W : Set ↥L) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer (W : Set ↥L))
    refine sup_le ?_ (Subgroup.center_le_centralizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hI'C (hWI hw))
  have hEXW : EX ≤ Subgroup.normalizer (W : Set ↥L) := by
    rw [hEXeq]
    exact sup_le hDW (Subgroup.zpowers_le.2 hWN)
  set U₀ : Subgroup G := W.map L.subtype with hU₀
  have hU₀card : Nat.card U₀ = 4 := by
    rw [hU₀, Subgroup.card_map_of_injective L.subtype_injective, hWcard]
  have hU₀el : CFSG.Assembly.IsElemAbelian 2 U₀ := by
    rw [isElemAbelian_iff]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
      exact congrArg Subtype.val (hWcomm w hw w' hw')
    · rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (hW2 w hw)
  have hEN : E ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro x hx
    have hxL : x ∈ L := hEL hx
    have hxEX : (⟨x, hxL⟩ : ↥L) ∈ EX := (hEXmem _).2 hx
    exact Subgroup.le_normalizer_map L.subtype
      (Subgroup.mem_map_of_mem L.subtype (hEXW hxEX))
  have hU₀four : U₀ ∈ fourGroups E := mem_fourGroups_iff.2 ⟨hEN, hU₀el, hU₀card⟩
  have hiE : (i : G) ∈ E := (hEXmem i).1 hiEX
  have huU : (u : G) ∈ U₀ := ⟨u, by rw [hWeq]; exact Subgroup.subset_closure (Or.inl rfl), rfl⟩
  have hvU : (v : G) ∈ U₀ := ⟨v, by rw [hWeq]; exact Subgroup.subset_closure (Or.inr rfl), rfl⟩
  have hUcomm : U₀ = ⁅U₀, E⁆ := by
    apply le_antisymm
    · have hcm := comm_V4 i u v huu hvv hyu hyv
      have h1 : (v : G) ∈ U₀ := hvU
      have hvi : ⁅(v : G), (i : G)⁆ = (u : G) := congrArg Subtype.val hcm.1
      have hui : ⁅(u : G), (i : G)⁆ = (u : G) * v := congrArg Subtype.val hcm.2
      have hu : (u : G) ∈ ⁅U₀, E⁆ := by
        rw [← hvi]; exact Subgroup.commutator_mem_commutator hvU hiE
      have huv' : (u : G) * v ∈ ⁅U₀, E⁆ := by
        rw [← hui]; exact Subgroup.commutator_mem_commutator huU hiE
      have hv : (v : G) ∈ ⁅U₀, E⁆ := by
        have := mul_mem (inv_mem hu) huv'
        simpa using this
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hWeq] at hw
      induction hw using Subgroup.closure_induction with
      | mem y hy => rcases hy with rfl | rfl <;> assumption
      | one => exact one_mem _
      | mul a b _ _ ha hb => exact mul_mem ha hb
      | inv a _ ha => exact inv_mem ha
    · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      have hyN := Subgroup.mem_normalizer_iff.1 (hEN hy) x⁻¹
      have h2 : y * x⁻¹ * y⁻¹ ∈ U₀ := hyN.1 (inv_mem hx)
      have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem hx h2
  refine ⟨U₀, ⟨hU₀four, hUcomm⟩, ?_, ?_⟩
  · rw [hI]
    exact Subgroup.map_mono hWI
  · intro b hb
    obtain ⟨hbE, hbC⟩ := hb
    have hbL : b ∈ L := hEL hbE
    have hbEX : (⟨b, hbL⟩ : ↥L) ∈ EX := (hEXmem _).2 hbE
    rw [hEXeq] at hbEX
    have hDi : ∀ x ∈ D, ∀ y ∈ Subgroup.zpowers i, x * y = y * x := by
      intro x hx y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((show Commute x i from hDcomm x hx i (hI'C hi)).zpow_right j).eq
    obtain ⟨d', hd', z, hz, hdz⟩ := (mem_sup_of_commute hDi).1 hbEX
    have hbu : (u : G) * b = b * u := Subgroup.mem_centralizer_iff.1 hbC u huU
    have hbX : u * (⟨b, hbL⟩ : ↥L) = (⟨b, hbL⟩ : ↥L) * u := Subtype.ext hbu
    rw [← hdz] at hbX
    have hd'u : d' * u = u * d' := hDcomm d' hd' u (hI'C huI)
    have hzu : u * z = z * u := by
      have h1 : d' * (u * z) = d' * (z * u) := by
        calc d' * (u * z) = (d' * u) * z := by rw [mul_assoc]
          _ = (u * d') * z := by rw [hd'u]
          _ = u * (d' * z) := by rw [mul_assoc]
          _ = d' * z * u := hbX
          _ = d' * (z * u) := by rw [mul_assoc]
      exact mul_left_cancel h1
    have hz1 : z = 1 := by
      rcases mem_zpowers_of_pow_three hi3 hz with h1 | h1 | h1
      · exact h1
      · exfalso
        rw [h1] at hzu
        apply hne
        have : i * u * i⁻¹ = u := by rw [← hzu]; group
        rw [hyu] at this
        exact this.symm
      · exfalso
        rw [h1] at hzu
        apply hv1
        have hzu' : u * (i * i) = (i * i) * u := by rw [← sq]; exact hzu
        have e1 : (i * i) * u * (i * i)⁻¹ = u := by rw [← hzu']; group
        have e2 : (i * i) * u * (i * i)⁻¹ = u * v := by
          have : (i * i) * u * (i * i)⁻¹ = i * (i * u * i⁻¹) * i⁻¹ := by group
          rw [this, hyu, hyv]
        rw [e1] at e2
        exact (mul_eq_left.1 e2.symm)
    rw [hz1, mul_one] at hdz
    have hbD : (⟨b, hbL⟩ : ↥L) ∈ D := hdz ▸ hd'
    have := Subgroup.mem_map_of_mem L.subtype hbD
    have hmapD : D.map L.subtype = Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
      rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers, h.map_center hθ]
      simp [ha'G]
    rw [hmapD] at this
    exact this

theorem nonCentral_sq {Q : Type*} [Group Q] {y : Q} (hy3 : y ^ 3 = 1) (h : NonCentral 3 y) :
    NonCentral 3 (y ^ 2) := by
  intro S hS
  apply h S
  have : y = (y ^ 2) ^ 2 := by
    have : (y ^ 2) ^ 2 = y ^ 3 * y := by group
    rw [this, hy3, one_mul]
  rw [this]
  exact pow_mem hS 2

theorem centralizer_eq_of_mul_central {X : Type*} [Group X] {a x z : X} (ha3 : a ^ 3 = 1)
    (hz : z ∈ Subgroup.center X) (hx : x = a ∨ x = a ^ 2) :
    Subgroup.centralizer ({x * z} : Set X) = Subgroup.centralizer ({a} : Set X) := by
  have hcom : ∀ y : X, Commute y z := fun y => (Subgroup.mem_center_iff.1 hz y)
  ext y
  simp only [Subgroup.mem_centralizer_singleton_iff]
  have h1 : y * (x * z) = x * z * y ↔ Commute y x := by
    constructor
    · intro h
      have : Commute y (x * z) := h
      have := this.mul_right (hcom y).inv_right
      simpa using this
    · intro h
      exact (h.mul_right (hcom y)).eq
  have h2 : Commute y x ↔ Commute y a := by
    rcases hx with rfl | rfl
    · exact Iff.rfl
    · constructor
      · intro h
        have : a = (a ^ 2) ^ 2 := by
          have : (a ^ 2) ^ 2 = a ^ 3 * a := by group
          rw [this, ha3, one_mul]
        rw [this]
        exact h.pow_right 2
      · intro h
        exact h.pow_right 2
  rw [h1]
  exact h2

set_option maxRecDepth 20000 in
theorem Cover217.frame_of_mem_D {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hfr : Frame217 E c L a) {b : G} (hbE : b ∈ E) (hbD : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c)
    (hbc : b ∉ Subgroup.zpowers c) :
    Frame217 E c L b ∧ iCore L b = iCore L a := by
  have hEA : E ≤ A := h.pair.mem_E.2
  have ha := hfr.valid hEA
  obtain ⟨a', I', ha'G, ha'c, ha3, hI'C, -, hI, -, -, -, -, hNC⟩ := h.local_frame hθ hAL ha
  have hbL : b ∈ L := hAL (hEA hbE)
  set b' : ↥L := ⟨b, hbL⟩ with hb'
  have hmapD : (Subgroup.zpowers a' ⊔ Subgroup.center ↥L).map L.subtype =
      Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, h.map_center hθ]
    simp [ha'G]
  have hb'D : b' ∈ Subgroup.zpowers a' ⊔ Subgroup.center ↥L := by
    rw [← hmapD] at hbD
    obtain ⟨b'', hb'', hbb⟩ := hbD
    have : b'' = b' := Subtype.ext hbb
    rw [← this]; exact hb''
  obtain ⟨x, hx, z, hz, hxz⟩ := (mem_sup_of_commute (fun x _ y hy =>
    Subgroup.mem_center_iff.1 hy x)).1 hb'D
  have hQz : ((z : ↥L) : ↥L ⧸ Subgroup.center ↥L) = 1 := (QuotientGroup.eq_one_iff z).2 hz
  have ha3Q : (a' : ↥L ⧸ Subgroup.center ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ha3]; rfl
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hbc
    rw [hx1, one_mul] at hxz
    rw [← h.map_center hθ]
    exact ⟨b', hxz ▸ hz, rfl⟩
  have hxcases : x = a' ∨ x = a' ^ 2 := by
    rcases mem_zpowers_of_pow_three ha3 hx with h1 | h1 | h1
    · exact absurd h1 hx1
    · exact Or.inl h1
    · exact Or.inr h1
  have hcent : Subgroup.centralizer ({b'} : Set ↥L) = Subgroup.centralizer ({a'} : Set ↥L) := by
    rw [← hxz]; exact centralizer_eq_of_mul_central ha3 hz hxcases
  refine ⟨⟨hbE, hbc, ⟨b', ⟨1, one_mem _, by simp [hb']⟩, ?_⟩⟩, ?_⟩
  · have hbQ : (b' : ↥L ⧸ Subgroup.center ↥L) = (x : ↥L ⧸ Subgroup.center ↥L) := by
      rw [← hxz, QuotientGroup.mk_mul, hQz, mul_one]
    rw [hbQ]
    rcases hxcases with rfl | rfl
    · exact hNC
    · rw [QuotientGroup.mk_pow]; exact nonCentral_sq ha3Q hNC
  ·
    have hCg : ∀ g' : ↥L, Subgroup.centralizer ({(g' : G)} : Set G) ⊓ L =
        (Subgroup.centralizer ({g'} : Set ↥L)).map L.subtype := by
      intro g'
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨hx, hxL⟩
        exact ⟨⟨x, hxL⟩, Subtype.ext hx, rfl⟩
      · rintro ⟨x', hx', rfl⟩
        exact ⟨congrArg Subtype.val hx', x'.2⟩
    unfold iCore
    have hb'G : (b' : G) = b := rfl
    rw [← hb'G, hCg b', hcent, ← ha'G, hCg a']

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
