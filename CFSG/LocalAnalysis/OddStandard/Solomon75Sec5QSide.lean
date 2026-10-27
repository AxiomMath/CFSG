module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QAlt

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Total

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

open Classical in
@[expose] noncomputable def AhatModel.permX (M : AhatModel X n A) (c : X) : Perm (Fin n) :=
  if h : c ∈ normalizer (A : Set X) then M.perm c h else 1

theorem AhatModel.permX_of_mem (M : AhatModel X n A) {c : X} (h : c ∈ normalizer (A : Set X)) :
    M.permX c = M.perm c h := by
  simp only [AhatModel.permX, h, ↓reduceDIte]

theorem AhatModel.permX_mul (M : AhatModel X n A) (hn : 8 ≤ n) {c d : X}
    (hc : c ∈ normalizer (A : Set X)) (hd : d ∈ normalizer (A : Set X)) :
    M.permX (c * d) = M.permX c * M.permX d := by
  rw [M.permX_of_mem (Subgroup.mul_mem _ hc hd), M.permX_of_mem hc, M.permX_of_mem hd,
    M.perm_mul hn hc hd]

theorem AhatModel.permX_one (M : AhatModel X n A) (hn : 8 ≤ n) : M.permX 1 = 1 := by
  rw [M.permX_of_mem (Subgroup.one_mem _), M.perm_one hn]

theorem AhatModel.permX_inv (M : AhatModel X n A) (hn : 8 ≤ n) {c : X}
    (hc : c ∈ normalizer (A : Set X)) : M.permX c⁻¹ = (M.permX c)⁻¹ := by
  have h := M.permX_mul hn hc (Subgroup.inv_mem _ hc)
  rw [mul_inv_cancel, M.permX_one hn] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

theorem AhatModel.permX_conj (M : AhatModel X n A) (hn : 8 ≤ n) {c d : X}
    (hc : c ∈ normalizer (A : Set X)) (hd : d ∈ normalizer (A : Set X)) :
    M.permX (c * d * c⁻¹) = M.permX c * M.permX d * (M.permX c)⁻¹ := by
  rw [M.permX_mul hn (Subgroup.mul_mem _ hc hd) (Subgroup.inv_mem _ hc), M.permX_mul hn hc hd,
    M.permX_inv hn hc]

theorem AhatModel.permX_comm (M : AhatModel X n A) (hn : 8 ≤ n) {c d : X}
    (hc : c ∈ normalizer (A : Set X)) (hd : d ∈ normalizer (A : Set X)) :
    M.permX ⁅c, d⁆ = ⁅M.permX c, M.permX d⁆ := by
  simp only [commutatorElement_def]
  rw [M.permX_mul hn (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hd) (Subgroup.inv_mem _ hc))
    (Subgroup.inv_mem _ hd), M.permX_mul hn (Subgroup.mul_mem _ hc hd) (Subgroup.inv_mem _ hc),
    M.permX_mul hn hc hd, M.permX_inv hn hc, M.permX_inv hn hd]

theorem AhatModel.permX_eq_one_iff (M : AhatModel X n A) (hn : 8 ≤ n) {c : X}
    (hc : c ∈ normalizer (A : Set X)) : M.permX c = 1 ↔ CentModOdd A c := by
  rw [M.permX_of_mem hc]
  exact M.perm_eq_one_iff hn hc

theorem AhatModel.permX_of_mem_A (M : AhatModel X n A) (hn : 8 ≤ n) {a : X} (ha : a ∈ A) :
    M.permX a = M.C.ρ (M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A))) := by
  rw [M.permX_of_mem (Subgroup.le_normalizer ha)]
  exact M.perm_of_mem hn ha

end Total

section Lift

variable {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}

theorem AhatModel.exists_lift_cent (M : AhatModel X n A) {r : X}
    (hr : r ∈ normalizer (A : Set X)) (hr2 : r * r = 1) {x : M.K} (hx : M.autOf r hr x = x) :
    ∃ (u : X) (hu : u ∈ A), r * u = u * r ∧ M.e (QuotientGroup.mk (⟨u, hu⟩ : ↥A)) = x := by
  obtain ⟨a₀, rfl⟩ := M.surj_mk x
  have hfa : (a₀ : X)⁻¹ * (r * (a₀ : X) * r⁻¹) ∈ oddCoreOf A := by
    rw [M.autOf_mk] at hx
    have h3 := QuotientGroup.eq.1 (M.e.injective hx).symm
    rw [mem_oddCoreOf_iff]
    refine ⟨?_, h3⟩
    refine mul_mem (inv_mem a₀.2) ?_
    have := (conjAut hr a₀).2
    rwa [coe_conjAut] at this
  obtain ⟨p, hp, hfixp⟩ := exists_fixed_mem_coset (odd_card_oddCoreOf A)
    (a := r) (k := 1) (by simpa [sq] using hr2)
    (mem_normalizer_oddCoreOf_of_mem_normalizer hr) hfa
  have hxA : (a₀ : X) * p ∈ A := mul_mem a₀.2 (oddCoreOf_le A hp)
  refine ⟨(a₀ : X) * p, hxA, ?_, ?_⟩
  · have : r * ((a₀ : X) * p) * r⁻¹ = (a₀ : X) * p := hfixp
    calc r * ((a₀ : X) * p) = (r * ((a₀ : X) * p) * r⁻¹) * r := by group
      _ = ((a₀ : X) * p) * r := by rw [this]
  · congr 1
    rw [QuotientGroup.eq]
    have : (⟨(a₀ : X) * p, hxA⟩ : ↥A)⁻¹ * a₀ = ⟨p⁻¹, inv_mem (oddCoreOf_le A hp)⟩ := by
      apply Subtype.ext
      simp
    rw [this]
    exact (mem_oddCoreOf_iff.1 (inv_mem hp)).2

end Lift

section Trivial

variable {X : Type} [Group X] [Finite X]

theorem centModOdd_of_comm_oddCore {A : Subgroup X} {r s : X}
    (hr : r ∈ normalizer (A : Set X)) (hs : s ∈ normalizer (A : Set X)) (hr2 : r * r = 1)
    (hrs : r * s = s * r) (hQ : CentModOdd A r)
    (hcs : ∀ c ∈ centralizer ({r} : Set X), ⁅c, s⁆ ∈ oddCoreOf (centralizer ({r} : Set X))) :
    CentModOdd A s := by
  set U : Subgroup X := A ⊓ centralizer ({r} : Set X) with hU
  have hcov : ∀ k ∈ A, ∃ u ∈ U, ∃ o ∈ oddCoreOf A, k = u * o := by
    intro k hk
    have h1 : k⁻¹ * (r * k * r⁻¹) ∈ oddCoreOf A := by
      have := hQ k⁻¹ (inv_mem hk)
      simpa [commutatorElement_def, mul_assoc] using this
    obtain ⟨p, hp, hfixp⟩ := exists_fixed_mem_coset (odd_card_oddCoreOf A) (a := r) (k := 1)
      (by simpa [sq] using hr2) (mem_normalizer_oddCoreOf_of_mem_normalizer hr) h1
    refine ⟨k * p, ⟨mul_mem hk (oddCoreOf_le A hp),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, p⁻¹, inv_mem hp, by group⟩
    have : r * (k * p) * r⁻¹ = k * p := hfixp
    calc k * p * r = (r * (k * p) * r⁻¹) * r := by rw [this]
      _ = r * (k * p) := by group
  have hOU : oddCoreOf U = U ⊓ oddCoreOf A :=
    oddCoreOf_eq_inf_of_cover inf_le_left hcov
  have hsU : ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro u hu
    refine ⟨(Subgroup.mem_normalizer_iff.1 hs u).1 hu.1,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : r * u = u * r := (Subgroup.mem_centralizer_singleton_iff.1 hu.2).symm
    have h2 : r * s⁻¹ = s⁻¹ * r := by
      calc r * s⁻¹ = s⁻¹ * (s * r) * s⁻¹ := by group
        _ = s⁻¹ * (r * s) * s⁻¹ := by rw [hrs]
        _ = s⁻¹ * r := by group
    calc s * u * s⁻¹ * r = s * u * (s⁻¹ * r) := by group
      _ = s * u * (r * s⁻¹) := by rw [h2]
      _ = s * (u * r) * s⁻¹ := by group
      _ = s * (r * u) * s⁻¹ := by rw [h1]
      _ = r * (s * u * s⁻¹) := by
        calc s * (r * u) * s⁻¹ = (s * r) * u * s⁻¹ := by group
          _ = (r * s) * u * s⁻¹ := by rw [hrs]
          _ = r * (s * u * s⁻¹) := by group
  have hcomm : ∀ u ∈ U, ⁅u, s⁆ ∈ oddCoreOf A := by
    intro u hu
    have hmemU : ⁅u, s⁆ ∈ U := by
      have : ⁅u, s⁆ = u * (s * u⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem hu (hsU u⁻¹ (inv_mem hu))
    have hmemO : ⁅u, s⁆ ∈ oddCoreOf (centralizer ({r} : Set X)) := hcs u hu.2
    have hle : U ⊓ oddCoreOf (centralizer ({r} : Set X)) ≤ oddCoreOf U := by
      refine le_oddCoreOf_of_normalized inf_le_left ?_ ?_
      · intro a ha
        exact mem_normalizer_inf (Subgroup.le_normalizer ha)
          (le_normalizer_oddCoreOf _ ha.2)
      · exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_right)
    rw [hOU] at hle
    exact (hle ⟨hmemU, hmemO⟩).2
  intro k hk
  obtain ⟨u, hu, o, ho, rfl⟩ := hcov k hk
  have hsO : s ∈ normalizer (oddCoreOf A : Set X) := mem_normalizer_oddCoreOf_of_mem_normalizer hs
  have e1 : ⁅u * o, s⁆ = u * ⁅o, s⁆ * u⁻¹ * ⁅u, s⁆ := by
    simp only [commutatorElement_def]; group
  have h2 : ⁅o, s⁆ ∈ oddCoreOf A := by
    have : ⁅o, s⁆ = o * (s * o⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ho ((Subgroup.mem_normalizer_iff.1 hsO o⁻¹).1 (inv_mem ho))
  have h3 : u * ⁅o, s⁆ * u⁻¹ ∈ oddCoreOf A :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf A hu.1) _).1 h2
  rw [e1]
  exact mul_mem h3 (hcomm u hu)

end Trivial

section Fixed

variable {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}

theorem AhatModel.fixed_of_comm_oddCore (M : AhatModel X n A) (hn : 8 ≤ n) {r s : X}
    (hr : r ∈ normalizer (A : Set X)) (hs : s ∈ normalizer (A : Set X)) (hr2 : r * r = 1)
    (hrs : r * s = s * r)
    (hcs : ∀ c ∈ centralizer ({r} : Set X), ⁅c, s⁆ ∈ oddCoreOf (centralizer ({r} : Set X)))
    (hF : 4 ≤ fixCount (M.permX r)) : ∀ i, M.permX r i = i → M.permX s i = i := by
  classical
  have : Finite M.K := Finite.of_equiv _ M.e.toEquiv
  have hσrσs : M.permX s * M.permX r = M.permX r * M.permX s := by
    rw [← M.permX_mul hn hs hr, ← M.permX_mul hn hr hs, hrs]
  set U : Subgroup X := A ⊓ centralizer ({r} : Set X) with hU
  set W : Subgroup X := U ⊓ oddCoreOf (centralizer ({r} : Set X)) with hW
  have hUN : U ≤ normalizer (A : Set X) := inf_le_left.trans Subgroup.le_normalizer
  have hWN : W ≤ normalizer (A : Set X) := inf_le_left.trans hUN
  let φ : ↥(normalizer (A : Set X)) →* Perm (Fin n) := M.permHom hn
  have hφ : ∀ (c : X) (hc : c ∈ normalizer (A : Set X)), φ ⟨c, hc⟩ = M.permX c := fun c hc =>
    (M.permX_of_mem hc).symm
  let N₀ : Subgroup (Perm (Fin n)) := (W.subgroupOf (normalizer (A : Set X))).map φ
  have hN₀ : ∀ y, y ∈ N₀ ↔ ∃ w : X, w ∈ W ∧ M.permX w = y := by
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by rw [← hφ w.1 w.2]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hWN hw⟩, hw, hφ w (hWN hw)⟩
  have hWodd : Odd (Nat.card W) :=
    Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_right)
  have hN₀odd : Odd (Nat.card N₀) := by
    have h1 : Nat.card N₀ ∣ Nat.card (W.subgroupOf (normalizer (A : Set X))) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (W.subgroupOf (normalizer (A : Set X))) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hWodd h1
  have hlift : ∀ a ∈ AhatData.altFixOf (M.permX r), ∃ u ∈ U, M.permX u = a := by
    intro a ha
    have hind := M.induces_perm hn r hr
    rw [← M.permX_of_mem hr] at hind
    obtain ⟨x, hx, hxa⟩ := hind.exists_mem_fixSub_of_mem_altFixOf ha
    obtain ⟨u, hu, hru, hux⟩ := M.exists_lift_cent hr hr2 (AhatData.mem_fixSub.1 hx)
    refine ⟨u, ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 hru.symm⟩, ?_⟩
    rw [M.permX_of_mem_A hn hu, hux, hxa]
  have hcommW : ∀ u ∈ U, ⁅u, s⁆ ∈ W := by
    intro u hu
    have hsr : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
    have e1 : ⁅u, s⁆ = u * (s * u⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    refine ⟨⟨?_, ?_⟩, hcs u hu.2⟩
    · rw [e1]
      exact mul_mem hu.1 ((Subgroup.mem_normalizer_iff.1 hs u⁻¹).1 (inv_mem hu.1))
    · have hc : ⁅u, s⁆ ∈ centralizer ({r} : Set X) := by
        simp only [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu.2 hsr)
          (Subgroup.inv_mem _ hu.2)) (Subgroup.inv_mem _ hsr)
      exact hc
  set N₁ : Subgroup (Perm (Fin n)) := N₀ ⊓ AhatData.altFixOf (M.permX r) with hN₁
  have hN₁le : N₁ ≤ AhatData.altFixOf (M.permX r) := inf_le_right
  have hconjW : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
    intro u hu w hw
    have hu' : u ∈ U := hu
    have hw' : w ∈ U ⊓ oddCoreOf (centralizer ({r} : Set X)) := hw
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hu' hw'.1) (Subgroup.inv_mem _ hu'),
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ hu'.2) w).1 hw'.2⟩
  have hN₁norm : ∀ b ∈ AhatData.altFixOf (M.permX r), ∀ y ∈ N₁, b * y * b⁻¹ ∈ N₁ := by
    intro b hb y hy
    obtain ⟨u, hu, rfl⟩ := hlift b hb
    obtain ⟨w, hw, rfl⟩ := (hN₀ y).1 hy.1
    refine ⟨(hN₀ _).2 ⟨u * w * u⁻¹, hconjW u hu w hw, ?_⟩, ?_⟩
    · exact M.permX_conj hn (hUN hu) (hWN hw)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hy.2) (Subgroup.inv_mem _ hb)
  have hN₁odd : Odd (Nat.card N₁) :=
    Odd.of_dvd_nat hN₀odd (Subgroup.card_dvd_of_le inf_le_left)
  have hF' : 4 ≤ (Finset.univ.filter fun i => M.permX r i = i).card := hF
  have hbot : N₁ = ⊥ := altFixOf_odd_normal_eq_bot hF' hN₁le hN₁norm hN₁odd
  have hcomm : ∀ a ∈ AhatData.altFixOf (M.permX r), a * M.permX s = M.permX s * a := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := hlift a ha
    have hsa : s ∈ normalizer (A : Set X) := hs
    have hc1 : ⁅M.permX u, M.permX s⁆ ∈ N₀ :=
      (hN₀ _).2 ⟨⁅u, s⁆, hcommW u hu, M.permX_comm hn (hUN hu) hs⟩
    have hconj : M.permX s * (M.permX u)⁻¹ * (M.permX s)⁻¹ ∈ AhatData.altFixOf (M.permX r) := by
      have h1 := (AhatData.mem_altFixOf_conj (M.permX r) (M.permX u)⁻¹ (M.permX s)⁻¹).1
      have h2 : (M.permX s)⁻¹ * M.permX r * ((M.permX s)⁻¹)⁻¹ = M.permX r := by
        have : M.permX r * M.permX s = M.permX s * M.permX r := hσrσs.symm
        calc (M.permX s)⁻¹ * M.permX r * ((M.permX s)⁻¹)⁻¹
            = (M.permX s)⁻¹ * (M.permX r * M.permX s) := by group
          _ = M.permX r := by rw [this]; group
      rw [h2] at h1
      simpa using h1 (Subgroup.inv_mem _ ha)
    have hc2 : ⁅M.permX u, M.permX s⁆ ∈ AhatData.altFixOf (M.permX r) := by
      have : ⁅M.permX u, M.permX s⁆ = M.permX u * (M.permX s * (M.permX u)⁻¹ * (M.permX s)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact Subgroup.mul_mem _ ha hconj
    have hc3 : ⁅M.permX u, M.permX s⁆ ∈ N₁ := ⟨hc1, hc2⟩
    rw [hbot, Subgroup.mem_bot] at hc3
    exact commutatorElement_eq_one_iff_mul_comm.1 hc3
  exact fixes_of_comm_altFixOf hσrσs hF' hcomm

end Fixed

end CFSG.OddStandard.Solomon75
