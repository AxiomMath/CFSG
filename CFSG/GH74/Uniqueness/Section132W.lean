module

public import CFSG.GH74.Uniqueness.Section13Lift
public import CFSG.GH74.Uniqueness.Section1214Semi

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem A6.mem_normalizer_zHull (hZ : IsInvariantInvolutionSet Z) {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : g ∈ normalizer (zHull Z H : Set X) := by
  have himg : (MulAut.conj g).toMonoidHom '' (Z ∩ (H : Set X)) = Z ∩ (H : Set X) := by
    ext x
    constructor
    · rintro ⟨z, ⟨hzZ, hzH⟩, rfl⟩
      refine ⟨?_, (mem_normalizer_iff.mp hg z).mp hzH⟩
      have := hZ.2 z hzZ g⁻¹
      simpa using this
    · rintro ⟨hxZ, hxH⟩
      refine ⟨g⁻¹ * x * g, ⟨hZ.2 x hxZ g, ?_⟩, ?_⟩
      · have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hxH
        simpa using this
      · simp [mul_assoc]
  have hmap : (zHull Z H).map (MulAut.conj g).toMonoidHom = zHull Z H := by
    unfold zHull
    rw [MonoidHom.map_closure, himg]
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hmap]
    exact ⟨h, hh, by simp⟩
  · intro hh
    rw [← hmap] at hh
    obtain ⟨h', hh', heq⟩ := hh
    have : h' = h := by
      have h2 : g * h' * g⁻¹ = g * h * g⁻¹ := by simpa using heq
      simpa using h2
    rwa [← this]

theorem A6.even_card_psl2 {n : ℕ} (hn : 2 ≤ n) : Even (Nat.card (Theory.Comparator.PSL2Model n)) := by
  rw [show Nat.card (Theory.Comparator.PSL2Model n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) from
    Bender.card_psl2_even n (by omega)]
  exact Even.mul_right ((Nat.even_pow' (by omega)).mpr even_two) _

theorem A6.le_closure_of_psl2 {n : ℕ} (hn : 2 ≤ n) {W : Subgroup X}
    (φ : ↥W ≃* Theory.Comparator.PSL2Model n) {S : Set X}
    (hS : ∀ w ∈ W, w * w = 1 → w ≠ 1 → w ∈ S) : W ≤ closure S := by
  have hB : Bender.BenderType ↥W n 1 1 := .linear n hn φ
  have : IsSimpleGroup ↥W := hB.isSimple
  set S₀ : Set ↥W := {w | w * w = 1 ∧ w ≠ 1} with hS₀
  have hconj : Group.conjugatesOfSet S₀ ⊆ S₀ := by
    intro w hw
    obtain ⟨s, hs, hsw⟩ := Group.mem_conjugatesOfSet_iff.mp hw
    obtain ⟨c, rfl⟩ := isConj_iff.mp hsw
    refine ⟨?_, ?_⟩
    · calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
        _ = 1 := by rw [hs.1]; group
    · intro h1
      apply hs.2
      calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
  have hnormal : closure S₀ = normalClosure S₀ := by
    apply le_antisymm (closure_le _ |>.mpr subset_normalClosure)
    rw [normalClosure]
    exact closure_mono hconj
  have hne : closure S₀ ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hev : 2 ∣ Nat.card ↥W := by
      rw [Nat.card_congr φ.toEquiv]
      exact even_iff_two_dvd.mp (A6.even_card_psl2 hn)
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hev
    intro hbot
    have hw1 : w ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hw
      omega
    have hww : w * w = 1 := by rw [← sq, ← hw, pow_orderOf_eq_one]
    have hmem : w ∈ closure S₀ := subset_closure ⟨hww, hw1⟩
    rw [hbot, mem_bot] at hmem
    exact hw1 hmem
  have htop : closure S₀ = ⊤ := by
    have hN : (closure S₀).Normal := by rw [hnormal]; infer_instance
    rcases Subgroup.Normal.eq_bot_or_eq_top (closure S₀) with h | h
    · exact absurd h hne
    · exact h
  intro w hw
  have h1 : (⟨w, hw⟩ : ↥W) ∈ closure S₀ := by rw [htop]; exact mem_top _
  have h2 : w ∈ (closure S₀).map W.subtype := ⟨⟨w, hw⟩, h1, rfl⟩
  rw [MonoidHom.map_closure] at h2
  refine closure_mono ?_ h2
  rintro _ ⟨s, ⟨hss, hs1⟩, rfl⟩
  exact hS s s.2 (congrArg Subtype.val hss) (fun h => hs1 (Subtype.ext h))

theorem A6.exists_W
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) {c : Ctx12 Z M} {n e : ℕ}
    (hL : LData c n 1) {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2)
    (hBu : BenderSub Z M (cenHull Z u) n 3 e) {A : Subgroup X} (hAu : A ≤ cenHull Z u)
    (hAodd : Odd (Nat.card A)) (hAL : ∀ a ∈ A, ∀ y ∈ c.L, a * y = y * a) :
    ∃ W : Subgroup X, W ≤ zHull Z (centralizer (A : Set X)) ∧ W ≠ c.L ∧
      Nonempty (↥W ≃* Theory.Comparator.PSL2Model n) := by
  have hZ := S.invariant
  obtain ⟨⟨x, hxΔ, hxu, hconj⟩, -⟩ := h12.l127 c n 1 hL u hu hu2
  obtain ⟨hMu, hLu⟩ := h12.l129 c n 1 hL u hu hu2
  obtain ⟨y, hy, rfl⟩ := hxΔ
  obtain ⟨-, hyM⟩ := mem_inf.mp hy
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hAx : ∀ a ∈ A, a * (y * u) = (y * u) * a := by
    intro a ha
    have h1 : a * y = y * a := hAL a ha y (hL.m_le hyM)
    have h2 : u * a = a * u := mul_comm_of_mem_cenHull (hAu ha)
    calc a * (y * u) = (a * y) * u := by group
      _ = y * (a * u) := by rw [h1]; group
      _ = y * (u * a) := by rw [h2]
      _ = (y * u) * a := by group
  have hMx : ∀ m ∈ zHull Z M, m * (y * u) = (y * u) * m := by
    intro m hm
    have h1 : m * y = y * m := hL.sec126_zHull_comm hm hyM
    have h2 : u * m = m * u := hMu m hm
    calc m * (y * u) = (m * y) * u := by group
      _ = y * (m * u) := by rw [h1]; group
      _ = y * (u * m) := by rw [h2]
      _ = (y * u) * m := by group
  set c' : X →* X := (MulAut.conj g⁻¹).toMonoidHom with hc'
  have hc'v : ∀ w, c' w = g⁻¹ * w * g := fun w => by simp [hc']
  have hc'inj : Function.Injective c' := (MulAut.conj g⁻¹).injective
  set Y : Subgroup X := A.map c' with hY
  set E : Subgroup X := (zHull Z M).map c' with hE
  have hcomm_u : ∀ w, w * (y * u) = (y * u) * w → c' w ∈ centralizer ({u} : Set X) := by
    intro w hw
    rw [mem_centralizer_singleton_iff, hc'v]
    calc g⁻¹ * w * g * u = g⁻¹ * (w * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * w) * g := by rw [hg, hw]
      _ = u * (g⁻¹ * w * g) := by group
  have hYN : Y ≤ normalizer (cenHull Z u : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    exact A6.mem_normalizer_zHull hZ (le_normalizer (hcomm_u a (hAx a ha)))
  have hYodd : Odd (Nat.card Y) := by rw [hY, card_map_of_injective hc'inj]; exact hAodd
  have hEF : E ≤ cenHull Z u := by
    rw [hE]
    unfold zHull
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨z, ⟨hzZ, hzM⟩, rfl⟩
    refine ⟨?_, hcomm_u z (hMx z (subset_closure ⟨hzZ, hzM⟩))⟩
    rw [hc'v]
    exact hZ.2 z hzZ g
  have hEsq : ∀ w ∈ E, w * w = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul, hL.sec126_zHull_sq hm, map_one]
  have hEcard : Nat.card E = 2 ^ n := by rw [hE, card_map_of_injective hc'inj, hL.m_card]
  have hYE : ∀ b ∈ Y, ∀ w ∈ E, b * w = w * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨m, hm, rfl⟩
    rw [← map_mul, ← map_mul, hAL a ha m (hL.m_le hm)]
  obtain ⟨W', hW'F, hEW', hYW', ⟨φ⟩⟩ := A6.exists_psl2_centralized hBu.bender
    (A2.odd_card_center_of_benderSub hBu) hYN hYodd hEF hEsq hEcard hYE
  set c'' : X →* X := (MulAut.conj g).toMonoidHom with hc''
  have hc''v : ∀ w, c'' w = g * w * g⁻¹ := fun w => by simp [hc'']
  have hc''inj : Function.Injective c'' := (MulAut.conj g).injective
  refine ⟨W'.map c'', ?_, ?_, ⟨(W'.equivMapOfInjective c'' hc''inj).symm.trans φ⟩⟩
  ·
    refine A6.le_closure_of_psl2 hL.hn ((W'.equivMapOfInjective c'' hc''inj).symm.trans φ) ?_
    rintro _ ⟨w, hw, rfl⟩ hww hw1
    rw [hc''v] at hww hw1 ⊢
    have hww' : w * w = 1 := by
      have : g * (w * w) * g⁻¹ = 1 := by rw [← hww]; group
      calc w * w = g⁻¹ * (g * (w * w) * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have hw1' : w ≠ 1 := by
      rintro rfl
      exact hw1 (by group)
    have hwZ : w ∈ Z := hBu.invol w (hW'F hw) (orderOf_eq_prime (by rw [sq]; exact hww') hw1')
    refine ⟨?_, ?_⟩
    · have := hZ.2 w hwZ g⁻¹
      simpa using this
    · rw [SetLike.mem_coe, mem_centralizer_iff]
      intro a ha
      have h1 := hYW' (c' a) ⟨a, ha, rfl⟩ w hw
      rw [hc'v] at h1
      calc a * (g * w * g⁻¹) = g * ((g⁻¹ * a * g) * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
        _ = (g * w * g⁻¹) * a := by group
  ·
    intro hWL
    have hxW : ∀ w ∈ W'.map c'', w * (y * u) = (y * u) * w := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hc''v]
      have h1 : u * w = w * u := mul_comm_of_mem_cenHull (hW'F hw)
      rw [← hg]
      calc g * w * g⁻¹ * (g * u * g⁻¹) = g * (w * u) * g⁻¹ := by group
        _ = g * (u * w) * g⁻¹ := by rw [h1]
        _ = g * u * g⁻¹ * (g * w * g⁻¹) := by group
    rw [hWL] at hxW
    have hyL : (⟨y, hL.m_le hyM⟩ : ↥c.L) ∈ center ↥c.L := by
      rw [mem_center_iff]
      intro l
      apply Subtype.ext
      have h1 := hxW l l.2
      have h2 : u * l = l * u := mul_comm_of_mem_cenHull (hLu l.2)
      change (l : X) * y = y * l
      calc (l : X) * y = (l * (y * u)) * u⁻¹ := by group
        _ = ((y * u) * l) * u⁻¹ := by rw [h1]
        _ = y * (u * l) * u⁻¹ := by group
        _ = y * (l * u) * u⁻¹ := by rw [h2]
        _ = y * l := by group
    rw [hL.center_eq_bot, mem_bot] at hyL
    apply hxu
    have : y = 1 := congrArg Subtype.val hyL
    rw [this, one_mul]

end CFSG.GH74.Uniqueness
