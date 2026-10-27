module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11K
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Y
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P09K

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise commutatorElement

section P1

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem mem_zpowers_of_mul_self {g : G} (hg : g * g = 1) {a : G} (ha : a ∈ zpowers g) :
    a = 1 ∨ a = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hg, one_zpow, one_mul]

theorem mem_zpowers_t (hd : d.Hyp) {a : G} (ha : a ∈ zpowers d.t) : a = 1 ∨ a = d.t :=
  mem_zpowers_of_mul_self hd.t_mul_self ha

theorem P1_le_P : P1 d ≤ d.s56P := inf_le_left

theorem P1_eps_inj (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) {x s : G} (hx : x ∈ P1 d) (hs : s ∈ P1 d) (h : d.s56Eps x = d.s56Eps s) :
    x * s⁻¹ ∈ d.F := by
  have hxP := P1_le_P hx
  have hsP := P1_le_P hs
  have hB : x * s⁻¹ ∈ d.B := by
    refine hd.s56_mem_B_of_eps_one h49 (mul_mem hxP (inv_mem hsP)) ?_
    rw [hd.s56_eps_mul_P h49 hxP (inv_mem hsP), hd.s56_eps_inv_P h49 hsP, h]
    exact hd.s56_eps_sq_P h49 hsP
  rw [← P1_inf_B h49 hd hz h07 h08]
  exact mem_inf.2 ⟨mul_mem hx (inv_mem hs), hB⟩

theorem epsImg_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    epsImg h49 hd (P1 d) = d.F := by
  have hsq := z0_sq hz h10
  obtain ⟨y, hy⟩ := h07.1
  refine epsImg_eq_F h49 hd (fun n hn s hs => P1_inv h49 hd hz hsq hy hn hs) ?_
  have h1 := epsImg_mono h49 hd (Kc_le_P1 h49 hd hz h07 h08 h09 h10)
  have h2 : Nat.card (epsImg h49 hd (K0 d z₀ ⊔ d.F)) = 16 := by
    rw [epsImg_Kc h49 hd hz h07 h08 h09 h10]
    exact hd.s56_card_E_inf_F
  have := Subgroup.card_le_of_le h1
  omega

theorem card_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) : Nat.card (P1 d) = 2 ^ 10 := by
  have h := card_eq_epsImg h49 hd (P1_le_P (d := d))
  rw [P1_inf_B h49 hd hz h07 h08, epsImg_P1 h49 hd hz h07 h08 h09 h10, hd.B_facts.1] at h
  rw [h]
  norm_num

theorem P_eq_zpowers_P1 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    (d.s56P : Set G) = (zpowers d.t : Set G) * (P1 d : Set G) := by
  have hsq := z0_sq hz h10
  obtain ⟨y, hy⟩ := h07.1
  refine P_eq_zpowers_mul h49 hd P1_le_P (F_le_P1 h49 hd h08)
    (fun n hn s hs => P1_inv h49 hd hz hsq hy hn hs) ?_
  rw [epsImg_P1 h49 hd hz h07 h08 h09 h10, hd.B_facts.1]
  norm_num

theorem mem_Pe10_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {x : G} :
    x ∈ Pe10 d ↔ x ∈ P1 d ∧ d.s56Eps x ∈ d.s56U10 := by
  constructor
  · rintro ⟨hxP1, -, hxt⟩
    have hxN : x ∈ d.N := d.s56_P_le_N (P1_le_P hxP1)
    refine ⟨hxP1, ?_⟩
    have := hxt d.t (mem_zpowers _)
    rwa [hd.s56_comm_t_eq_eps h49 hxN] at this
  · rintro ⟨hxP1, hε⟩
    have hxN : x ∈ d.N := d.s56_P_le_N (P1_le_P hxP1)
    refine ⟨hxP1, ?_, fun a ha => ?_⟩
    · rw [mem_normalizer_iff]
      intro u
      refine ⟨fun hu => hd.s56_N_conj_U10 h49 hxN hu, fun hu => ?_⟩
      have := hd.s56_N_conj_U10 h49 (inv_mem hxN) hu
      simpa [mul_assoc] using this
    · rcases mem_zpowers_t hd ha with rfl | rfl
      · simpa using one_mem d.s56U10
      · rwa [hd.s56_comm_t_eq_eps h49 hxN]

theorem Pe10_le_P1 : Pe10 d ≤ P1 d := fun _ hx => hx.1

theorem Pe_le_Pe10 (h49 : d.Thm49Statement) (hd : d.Hyp) (h08 : Node08 d z₀) :
    Pe11 d ≤ Pe10 d := by
  intro x hx
  refine (mem_Pe10_iff h49 hd).2 ⟨Pe_le_P1 h49 hd h08 hx, ?_⟩
  have hx11 : x ∈ d.s56P11 := by
    rw [Pe11_eq_s56Pe11] at hx
    exact hd.s56_Pe11_le_P11 h49 hx
  exact Data.s56_U11_le_U10 d ((hd.s56_mem_P11_iff h49).1 hx11).2

theorem Pe10_inv (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h10 : Node10 d z₀) {n : G} (hn : n ∈ d.N) {x : G} (hx : x ∈ Pe10 d) : n * x * n⁻¹ ∈ Pe10 d := by
  have hsq := z0_sq hz h10
  obtain ⟨y, hy⟩ := h07.1
  obtain ⟨hxP1, hε⟩ := (mem_Pe10_iff h49 hd).1 hx
  refine (mem_Pe10_iff h49 hd).2 ⟨P1_inv h49 hd hz hsq hy hn hxP1, ?_⟩
  rw [hd.s56_eps_conj_N h49 hn (P1_le_P hxP1)]
  exact hd.s56_N_conj_U10 h49 hn hε

theorem exists_u (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    ∃ u ∈ K0 d z₀, u * d.t * u⁻¹ * d.t⁻¹ = d.pv 10 ∧ Pe10 d = Pe11 d ⊔ zpowers u := by
  have h10E : d.pv 10 ∈ epsImg h49 hd (K0 d z₀) := by
    rw [epsImg_K0 h49 hd hz h07 h08 h09 h10]
    exact mem_inf.2 ⟨hd.s56_pv10_mem_E, Data.s56_pv10_mem_F d⟩
  obtain ⟨u, huK, huP, huε⟩ := (mem_epsImg h49 hd).1 h10E
  have huP1 : u ∈ P1 d := Kc_le_P1 h49 hd hz h07 h08 h09 h10 (mem_sup_left huK)
  have huN : u ∈ d.N := d.s56_P_le_N huP
  refine ⟨u, huK, ?_, ?_⟩
  · rw [hd.s56_comm_t_eq_eps h49 huN, huε]
  · have huPe10 : u ∈ Pe10 d := (mem_Pe10_iff h49 hd).2 ⟨huP1, by rw [huε]; exact Data.s56_pv10_mem_U10 d⟩
    refine le_antisymm (fun x hx => ?_) (sup_le (Pe_le_Pe10 h49 hd h08) (zpowers_le.2 huPe10))
    obtain ⟨hxP1, hxε⟩ := (mem_Pe10_iff h49 hd).1 hx
    have hxP := P1_le_P hxP1
    have hFPe : d.F ≤ Pe11 d := h08.2.1
    rcases Data.s56_U10_cases hxε with h | ⟨a, ha, hxa⟩
    ·
      obtain ⟨w, hw, hwε⟩ := hd.s56_eps_Pe11_surj_Y h49 hz _ h
      have hwP1 : w ∈ P1 d := Pe_le_P1 h49 hd h08 (by rwa [Pe11_eq_s56Pe11])
      have hf := P1_eps_inj h49 hd hz h07 h08 hxP1 hwP1 hwε.symm
      have : x = (x * w⁻¹) * w := by group
      rw [this]
      exact mul_mem (mem_sup_left (hFPe hf)) (mem_sup_left (by rwa [Pe11_eq_s56Pe11]))
    ·
      obtain ⟨w, hw, hwε⟩ := hd.s56_eps_Pe11_surj_Y h49 hz _ ha
      have hwP1 : w ∈ P1 d := Pe_le_P1 h49 hd h08 (by rwa [Pe11_eq_s56Pe11])
      have hwP : w ∈ d.s56P := P1_le_P hwP1
      have huwP1 : u * w ∈ P1 d := mul_mem huP1 hwP1
      have hε' : d.s56Eps x = d.s56Eps (u * w) := by
        rw [hd.s56_eps_mul_P h49 huP hwP, huε, hwε, hxa]
      have hf := P1_eps_inj h49 hd hz h07 h08 hxP1 huwP1 hε'
      have : x = (x * (u * w)⁻¹) * u * w := by group
      rw [this]
      exact mul_mem (mul_mem (mem_sup_left (hFPe hf)) (mem_sup_right (mem_zpowers u)))
        (mem_sup_left (by rwa [Pe11_eq_s56Pe11]))

theorem Pe10_le_Kc (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    Pe10 d ≤ K0 d z₀ ⊔ d.F := by
  obtain ⟨u, huK, -, hPe⟩ := exists_u h49 hd hz h07 h08 h09 h10
  rw [hPe]
  exact sup_le (Pe_le_Kc h49 hd hz h07 h08 h09 h10) (zpowers_le.2 (mem_sup_left huK))

theorem Pe10_central (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    ∀ x ∈ Pe10 d, ∀ p ∈ P1 d, x * p = p * x := by
  have hsq := z0_sq hz h10
  obtain ⟨y, hy⟩ := h07.1
  have hKcP1 := Kc_le_P1 h49 hd hz h07 h08 h09 h10
  have hKcc := Kc_comm h49 hd hz h07 h08 h09 h10
  have hPe10Kc := Pe10_le_Kc h49 hd hz h07 h08 h09 h10
  let C : Subgroup G := d.s56P ⊓ centralizer ((Pe10 d : Subgroup G) : Set G)
  have hCP : C ≤ d.s56P := inf_le_left
  have hCc : ∀ c ∈ C, ∀ x ∈ Pe10 d, x * c = c * x := fun c hc x hx =>
    mem_centralizer_iff.1 (mem_inf.1 hc).2 x hx
  have hCinv : ∀ n ∈ d.N, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    refine mem_inf.2 ⟨hd.s56_N_conj_P h49 hn (hCP hc), mem_centralizer_iff.2 fun x hx => ?_⟩
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ Pe10 d := Pe10_inv h49 hd hz h07 h10 (inv_mem hn) hx
    have h := hCc c hc _ hx'
    calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n⁻¹⁻¹) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
      _ = (n * c * n⁻¹) * x := by group
  have hFC : d.F ≤ C := fun f hf => mem_inf.2 ⟨hd.s56_B_le_P (s56_F_le_B d hf),
    mem_centralizer_iff.2 fun x hx => hKcc _ (hPe10Kc hx) f (mem_sup_right hf)⟩
  have hKC : K0 d z₀ ⊔ d.F ≤ C := fun k hk => mem_inf.2 ⟨P1_le_P (hKcP1 hk),
    mem_centralizer_iff.2 fun x hx => hKcc _ (hPe10Kc hx) k hk⟩
  have hεC : 16 ≤ Nat.card (epsImg h49 hd C) := by
    have h1 := epsImg_mono h49 hd hKC
    have h2 : Nat.card (epsImg h49 hd (K0 d z₀ ⊔ d.F)) = 16 := by
      rw [epsImg_Kc h49 hd hz h07 h08 h09 h10]
      exact hd.s56_card_E_inf_F
    have := Subgroup.card_le_of_le h1
    omega
  have hP := P_eq_zpowers_mul h49 hd hCP hFC hCinv hεC
  have hCP1 : C ≤ P1 d := fun c hc => mem_P1_iff.2 ⟨hCP hc, fun w hw =>
    hCc c hc w (Pe_le_Pe10 h49 hd h08 hw)⟩
  intro x hx p hp
  have hpC : p ∈ C := by
    have hpP : p ∈ ((d.s56P : Subgroup G) : Set G) := P1_le_P hp
    rw [hP] at hpP
    obtain ⟨a, ha, c, hc, hac⟩ := hpP
    have hac' : a * c = p := hac
    rcases mem_zpowers_t hd ha with rfl | rfl
    · rw [one_mul] at hac'
      rw [← hac']
      exact hc
    · exfalso
      apply t_not_mem_P1 hd hz h07 h08
      have : d.t = p * c⁻¹ := by rw [← hac']; group
      rw [this]
      exact mul_mem hp (inv_mem (hCP1 hc))
  exact hCc p hpC x hx

theorem U10_le_epsImg_Pe10 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    d.s56U10 ≤ epsImg h49 hd (Pe10 d) := by
  obtain ⟨u, huK, hu, hPe⟩ := exists_u h49 hd hz h07 h08 h09 h10
  have huP1 : u ∈ P1 d := Kc_le_P1 h49 hd hz h07 h08 h09 h10 (mem_sup_left huK)
  have huP : u ∈ d.s56P := P1_le_P huP1
  have huN : u ∈ d.N := d.s56_P_le_N huP
  have huε : d.s56Eps u = d.pv 10 := by
    rw [← hd.s56_comm_t_eq_eps h49 huN]
    exact hu
  have hu10 : u ∈ Pe10 d :=
    (mem_Pe10_iff h49 hd).2 ⟨huP1, by rw [huε]; exact Data.s56_pv10_mem_U10 d⟩
  have h11 : ∀ a ∈ d.s56U11, a ∈ epsImg h49 hd (Pe10 d) := fun a ha => by
    obtain ⟨w, hw, hwε⟩ := hd.s56_eps_Pe11_surj_Y h49 hz a ha
    have hw' : w ∈ Pe11 d := by rwa [Pe11_eq_s56Pe11]
    exact (mem_epsImg h49 hd).2 ⟨w, Pe_le_Pe10 h49 hd h08 hw', Pe_le_P h49 hd hw', hwε⟩
  intro x hx
  rcases Data.s56_U10_cases hx with h | ⟨a, ha, rfl⟩
  · exact h11 x h
  · exact mul_mem ((mem_epsImg h49 hd).2 ⟨u, hu10, huP, huε⟩) (h11 a ha)

theorem exists_v (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) {y : G} (hy : IsY d y) :
    ∃ v ∈ K0 d z₀, v * d.t * v⁻¹ * d.t⁻¹ = d.pv 9 ∧
      P1 d = Pe10 d ⊔ Subgroup.closure ({v, y * v * y⁻¹} : Set G) := by
  have hsq := z0_sq hz h10
  obtain ⟨hyN, hy3, hy1⟩ := hy.facts
  have h9E : d.pv 9 ∈ epsImg h49 hd (K0 d z₀) := by
    rw [epsImg_K0 h49 hd hz h07 h08 h09 h10]
    exact mem_inf.2 ⟨node09K_pv9_mem_E d, node09K_pv9_mem_F d⟩
  obtain ⟨v, hvK, hvP, hvε⟩ := (mem_epsImg h49 hd).1 h9E
  have hvP1 : v ∈ P1 d := Kc_le_P1 h49 hd hz h07 h08 h09 h10 (mem_sup_left hvK)
  have hyvP1 : y * v * y⁻¹ ∈ P1 d := P1_inv h49 hd hz hsq hy hyN hvP1
  refine ⟨v, hvK, by rw [hd.s56_comm_t_eq_eps h49 (d.s56_P_le_N hvP), hvε], ?_⟩
  set S := Pe10 d ⊔ Subgroup.closure ({v, y * v * y⁻¹} : Set G) with hS
  have hSP1 : S ≤ P1 d := by
    refine sup_le Pe10_le_P1 ((Subgroup.closure_le _).2 ?_)
    rintro x (rfl | hx)
    · exact hvP1
    · rw [Set.mem_singleton_iff.1 hx]
      exact hyvP1
  refine le_antisymm (fun x hx => ?_) hSP1
  have hvS : v ∈ S := mem_sup_right (Subgroup.subset_closure (by simp))
  have hvyS : y * v * y⁻¹ ∈ S := mem_sup_right (Subgroup.subset_closure (by simp))
  have hF10 : d.F ≤ Pe10 d := h08.2.1.trans (Pe_le_Pe10 h49 hd h08)
  have hyvP : y * v * y⁻¹ ∈ d.s56P := hd.s56_N_conj_P h49 hyN hvP
  have hW : epsImg h49 hd S = d.F := by
    refine eq_F_of_mem_of_IsY h49 hd hy (epsImg_le_F h49 hd S)
      ((U10_le_epsImg_Pe10 h49 hd hz h07 h08 h09 h10).trans
        (epsImg_mono h49 hd (le_sup_left : Pe10 d ≤ S)))
      (node09K_pv9_mem_F d) (node09K_pv9_not_mem_U10 d) ?_ ?_
    · rw [← hvε]
      exact eps_mem_epsImg h49 hd hvS hvP
    · have : y * d.pv 9 * y⁻¹ = d.s56Eps (y * v * y⁻¹) := by
        rw [hd.s56_eps_conj_N h49 hyN hvP, hvε]
      rw [this]
      exact eps_mem_epsImg h49 hd hvyS hyvP
  have hxF : d.s56Eps x ∈ epsImg h49 hd S := by
    rw [hW]
    exact hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N (P1_le_P hx))
  obtain ⟨s, hsS, hsP, hsε⟩ := (mem_epsImg h49 hd).1 hxF
  have hf := P1_eps_inj h49 hd hz h07 h08 hx (hSP1 hsS) hsε.symm
  have : x = (x * s⁻¹) * s := by group
  rw [this]
  exact mul_mem (mem_sup_left (hF10 hf)) hsS

theorem P1_comm (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h07 : Node07 d)
    (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    ∀ a ∈ P1 d, ∀ b ∈ P1 d, a * b = b * a := by
  have hsq := z0_sq hz h10
  obtain ⟨y, hy⟩ := h07.1
  obtain ⟨hyN, hy3, hy1⟩ := hy.facts
  obtain ⟨v, hvK, hvε, hgen⟩ := exists_v h49 hd hz h07 h08 h09 h10 hy
  have hvP1 : v ∈ P1 d := Kc_le_P1 h49 hd hz h07 h08 h09 h10 (mem_sup_left hvK)
  have hvP : v ∈ d.s56P := P1_le_P hvP1
  set u := y * v * y⁻¹ with hu
  have huP1 : u ∈ P1 d := P1_inv h49 hd hz hsq hy hyN hvP1
  have huP : u ∈ d.s56P := P1_le_P huP1
  have hcen := Pe10_central h49 hd hz h07 h08 h09 h10
  have hF10 : d.F ≤ Pe10 d := h08.2.1.trans (Pe_le_Pe10 h49 hd h08)
  set c := v * u * v⁻¹ * u⁻¹ with hc
  have hcP1 : c ∈ P1 d := mul_mem (mul_mem (mul_mem hvP1 huP1) (inv_mem hvP1)) (inv_mem huP1)
  have hcP : c ∈ d.s56P := P1_le_P hcP1
  have hcF : c ∈ d.F := by
    have hεF := fun g (hg : g ∈ d.s56P) => hd.s56_eps_mem_F_of_N h49 (d.s56_P_le_N hg)
    have hcε : d.s56Eps c = 1 := by
      rw [hc, hd.s56_eps_mul_P h49 (mul_mem (mul_mem hvP huP) (inv_mem hvP)) (inv_mem huP),
        hd.s56_eps_mul_P h49 (mul_mem hvP huP) (inv_mem hvP),
        hd.s56_eps_mul_P h49 hvP huP, hd.s56_eps_inv_P h49 hvP, hd.s56_eps_inv_P h49 huP]
      have h1 := hεF v hvP
      have h2 := hεF u huP
      have hcomm := hd.s56_F_comm h1 h2
      calc d.s56Eps v * d.s56Eps u * d.s56Eps v * d.s56Eps u
          = d.s56Eps v * (d.s56Eps u * d.s56Eps v) * d.s56Eps u := by group
        _ = d.s56Eps v * (d.s56Eps v * d.s56Eps u) * d.s56Eps u := by rw [hcomm]
        _ = (d.s56Eps v * d.s56Eps v) * (d.s56Eps u * d.s56Eps u) := by group
        _ = 1 := by rw [hd.s56_F_sq h1, hd.s56_F_sq h2, one_mul]
    rw [← P1_inf_B h49 hd hz h07 h08]
    exact mem_inf.2 ⟨hcP1, hd.s56_mem_B_of_eps_one h49 hcP hcε⟩
  have hcPe10 : c ∈ Pe10 d := hF10 hcF
  have hcomm_le : ⁅P1 d, P1 d⁆ ≤ Subgroup.closure {c} :=
    commutator_le_closure_of_central (Γ := P1 d) (Z := Pe10 d) (a := v) (b := u)
      (fun z hz g hg => hcen z hz g hg) Pe10_le_P1 hvP1 huP1 hgen.le hcPe10
  have hc1 : c = 1 := by
    by_contra hne
    refine hne (CF_CNt_trivial h49 hd hcF fun n hn => ?_)
    have hnN : n ∈ d.N := (mem_inf.1 hn).1
    have hmem : n * c * n⁻¹ ∈ ⁅P1 d, P1 d⁆ := by
      have e : n * c * n⁻¹ = ⁅n * v * n⁻¹, n * u * n⁻¹⁆ := by
        simp only [hc, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (P1_inv h49 hd hz hsq hy hnN hvP1)
        (P1_inv h49 hd hz hsq hy hnN huP1)
    have hcc : c * c = 1 := hd.s56_F_sq hcF
    have hmem2 := hcomm_le hmem
    rw [← Subgroup.zpowers_eq_closure] at hmem2
    rcases mem_zpowers_of_mul_self hcc hmem2 with h | h
    · exfalso
      apply hne
      calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    · calc c * n = (n * c * n⁻¹) * n := by rw [h]
        _ = n * c := by group
  have huv : v * u = u * v := by
    have h1 : v * u * v⁻¹ * u⁻¹ = 1 := hc1
    have h2 : v * u * v⁻¹ = u := mul_inv_eq_one.1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hP1eq : P1 d = Subgroup.closure ((Pe10 d : Set G) ∪ {v, u}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq]
    exact hgen
  have hmemset : ∀ x ∈ ((Pe10 d : Set G) ∪ {v, u}), x ∈ P1 d := by
    intro x hx
    rcases hx with hx | hx
    · exact Pe10_le_P1 hx
    · rcases hx with rfl | hx
      · exact hvP1
      · rw [Set.mem_singleton_iff.1 hx]
        exact huP1
  have hkey : ∀ x ∈ ((Pe10 d : Set G) ∪ {v, u}), ∀ x' ∈ ((Pe10 d : Set G) ∪ {v, u}),
      x * x' = x' * x := by
    intro x hx x' hx'
    rcases hx with hx | hx
    · exact hcen x hx x' (hmemset x' hx')
    · rcases hx' with hx' | hx'
      · exact (hcen x' hx' x (hmemset x (Or.inr hx))).symm
      · rcases hx with rfl | hx
        · rcases hx' with rfl | hx'
          · rfl
          · rw [Set.mem_singleton_iff.1 hx']
            exact huv
        · rw [Set.mem_singleton_iff.1 hx]
          rcases hx' with rfl | hx'
          · exact huv.symm
          · rw [Set.mem_singleton_iff.1 hx']
  have hcomm : IsMulCommutative (P1 d) := by
    rw [hP1eq]
    exact Subgroup.isMulCommutative_closure fun x hx x' hx' _ => hkey x hx x' hx'
  intro a ha b hb
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end P1

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
