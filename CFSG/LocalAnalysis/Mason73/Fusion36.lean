module

public import CFSG.LocalAnalysis.Mason73.Fusion35b
public import CFSG.LocalAnalysis.Mason73.Model36
public import CFSG.LocalAnalysis.Mason73.Transfer

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.ABGLocalTools
  CFSG.ComponentClassification Equiv Subgroup

variable {G : Type} [Group G] [Finite G] {n : ℕ}

theorem exists_conj_trans {ι : L4Model n →* G} {a b c : L4Model n} {g h : G}
    (hg : g * ι a * g⁻¹ = ι b) (hh : h * ι b * h⁻¹ = ι c) : ∃ g' : G, g' * ι a * g'⁻¹ = ι c :=
  ⟨h * g, by rw [← hh, ← hg]; group⟩

theorem exists_conj_of_conj_isConj {ι : L4Model n →* G} {a b c : L4Model n} {g : G}
    (hg : g * ι a * g⁻¹ = ι b) (hbc : IsConj b c) : ∃ g' : G, g' * ι a * g'⁻¹ = ι c := by
  obtain ⟨x, rfl⟩ := isConj_iff.1 hbc
  refine ⟨ι x * g, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg]
  group

theorem ne_one_of_conj_eq {ι : L4Model n →* G} (hι : Function.Injective ι) {a b : L4Model n}
    (ha : a ≠ 1) {g : G} (hg : g * ι a * g⁻¹ = ι b) : b ≠ 1 := by
  rintro rfl
  apply ha
  apply hι
  rw [map_one]
  calc ι a = g⁻¹ * (g * ι a * g⁻¹) * g := by group
    _ = 1 := by rw [hg, map_one]; group

theorem exists_conj_y1T_zT (hn : 2 ≤ n) {ι : L4Model n →* G}
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) :
    ∃ g : G, g * ι (y1T (by omega)) * g⁻¹ = ι (zT (by omega)) := by
  obtain ⟨g, hg⟩ := hzx
  exact exists_conj_of_isConj (isConj_y1T_x1T hn) hg

theorem conj_zT_or_w1T_of_conj_mem_A (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) {l e : L4Model n}
    (he : e ∈ A n) (he2 : e * e = 1) (he1 : e ≠ 1) {g : G} (hg : g * ι l * g⁻¹ = ι e) :
    (∃ g' : G, g' * ι l * g'⁻¹ = ι (zT (by omega))) ∨
      ∃ g' : G, g' * ι l * g'⁻¹ = ι (w1T hn) := by
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn he he2
  rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hp | hp
  · have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
        q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
      decide
    left
    rcases key p hp with rfl | rfl | rfl | rfl
    · exact absurd (omegaEl_zero hn) he1
    · exact ⟨g, by rw [hg, zT_eq_omegaEl hn]⟩
    · obtain ⟨g₁, hg₁⟩ := hzx
      exact exists_conj_trans (by rw [hg, ← x1T_eq_omegaEl hn]) hg₁
    · obtain ⟨g₁, hg₁⟩ := exists_conj_y1T_zT (by omega) hzx
      exact exists_conj_trans (by rw [hg, ← y1T_eq_omegaEl hn]) hg₁
  · right
    obtain ⟨c, hc⟩ := exists_conj_w1T_eq hn p hp
    refine ⟨(ι c)⁻¹ * g, ?_⟩
    rw [show (ι c)⁻¹ * g * ι l * ((ι c)⁻¹ * g)⁻¹ = (ι c)⁻¹ * (g * ι l * g⁻¹) * ι c by group, hg,
      ← hc, map_mul, map_mul, map_inv]
    group

theorem isSylowOf_w1T (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤) :
    IsSylowOf 2 (ι.range ⊓ centralizer {ι (w1T hn)}) (centralizer {ι (w1T hn)}) := by
  refine GHarris.isSylowOf_of_card_le hS ⟨_, rfl⟩ fun g hg => ?_
  obtain ⟨ν, hν⟩ := hg
  rw [← hν, card_range_inf_centralizer hι, card_range_inf_centralizer hι,
    card_centralizer_w1T hn]
  have hgν : g⁻¹ * ι (w1T hn) * g⁻¹⁻¹ = ι ν := by rw [inv_inv, hν]
  refine card_centralizer_le hn (ne_one_of_conj_eq hι (w1T_ne_one hn) hgν)
    (mul_self_of_conj_eq hι (w1T_mul_self hn) hgν) ?_ ?_ ?_
  · rintro rfl
    exact not_conj_w1T_zT hn hι hS _ hgν
  · rintro rfl
    exact not_conj_w1T_x1T hn hι hS _ hgν
  · rintro rfl
    obtain ⟨g', hg'⟩ := exists_conj_of_conj_isConj hgν (isConj_y1T_x1T (by omega))
    exact not_conj_w1T_x1T hn hι hS g' hg'

theorem isSylowOf_of_piT_s23 (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) {l : L4Model n}
    (hl2 : l * l = 1) (hπ : piT l = s23) (hz : ∀ g : G, g * ι l * g⁻¹ ≠ ι (zT (by omega)))
    (hw : ∀ g : G, g * ι l * g⁻¹ ≠ ι (w1T hn)) :
    IsSylowOf 2 (ι.range ⊓ centralizer {ι l}) (centralizer {ι l}) := by
  refine GHarris.isSylowOf_of_card_le hS ⟨l, rfl⟩ fun g hg => ?_
  obtain ⟨ν, hν⟩ := hg
  rw [← hν, card_range_inf_centralizer hι, card_range_inf_centralizer hι,
    card_centralizer_of_piT_s23 hn hl2 (Or.inl hπ)]
  have hgν : g⁻¹ * ι l * g⁻¹⁻¹ = ι ν := by rw [inv_inv, hν]
  have hl1 : l ≠ 1 := fun h => by
    rw [h, map_one] at hπ
    exact absurd hπ (by decide)
  have hν2 := mul_self_of_conj_eq hι hl2 hgν
  refine card_centralizer_le_of_mul_self_not_mem_A hn hν2 fun hνA => ?_
  rcases conj_zT_or_w1T_of_conj_mem_A hn hzx hνA hν2 (ne_one_of_conj_eq hι hl1 hgν) hgν with
    ⟨g', hg'⟩ | ⟨g', hg'⟩
  · exact hz g' hg'
  · exact hw g' hg'

theorem index_Q2T : (V2.comap (piT (n := n))).index = 2 := by
  rw [Subgroup.index_comap_of_surjective _ piT_surjective]
  have h := Subgroup.card_mul_index V2
  rw [card_V2, Fin81.card_R0] at h
  omega

theorem piT_cases_of_mem_Q2T {q : L4Model n} (hq : q ∈ V2.comap piT) :
    piT q = 1 ∨ piT q = zP ∨ piT q = tP ∨ piT q = tzP := by
  have key : ∀ π : Fin81.R0, π ∈ V2 → π = 1 ∨ π = zP ∨ π = tP ∨ π = tzP := by
    decide
  exact key _ hq

theorem conj_zT_or_w1T_of_piT_s23 (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)))
    (hsqrt : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP → ∃ r : L4Model n, r * r = μ)
    (hE16 : ∀ μ : L4Model n, μ * μ = 1 → (piT μ = tP ∨ piT μ = tzP) →
      ∃ E : Subgroup (L4Model n), (∀ x ∈ E, x * x = 1) ∧ E ≤ centralizer {μ} ∧
        Nat.card E = 16)
    {l : L4Model n} (hl2 : l * l = 1) (hπ : piT l = s23) (hl : ι l ∈ commutator G) :
    (∃ g : G, g * ι l * g⁻¹ = ι (zT (by omega))) ∨ ∃ g : G, g * ι l * g⁻¹ = ι (w1T hn) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hz, hw⟩ := hcon
  have hext := isSylowOf_of_piT_s23 hn hι hS hzx hl2 hπ hz hw
  have hl1 : l ≠ 1 := fun h => by
    rw [h, map_one] at hπ
    exact absurd hπ (by decide)
  refine not_mem_commutator_of_not_conj_into hι hS index_Q2T
    (orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1) ?_ hl
  rintro x ⟨q, hq, hqx⟩
  have hlq : x⁻¹ * ι l * x⁻¹⁻¹ = ι q := by rw [inv_inv, hqx]
  have hql : x * ι q * x⁻¹ = ι l := by rw [hqx]; group
  have hq2 := mul_self_of_conj_eq hι hl2 hlq
  rcases piT_cases_of_mem_Q2T hq with h | h | h | h
  · rcases conj_zT_or_w1T_of_conj_mem_A hn hzx (mem_A_iff.2 h) hq2
      (ne_one_of_conj_eq hι hl1 hlq) hlq with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact hz g hg
    · exact hw g hg
  ·
    obtain ⟨r, hr⟩ := hsqrt q hq2 h
    obtain ⟨k, hkq, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup hext
      (u := ι q) (h := x) hqx.symm
    have hrq : ι r ∈ (ι.range ⊓ centralizer {ι q} : Subgroup G) := by
      refine Subgroup.mem_inf.2 ⟨⟨r, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← map_mul, ← map_mul, ← hr, mul_assoc]
    obtain ⟨⟨s, hs⟩, -⟩ := Subgroup.mem_inf.1 (hk _ hrq)
    apply mul_self_ne_of_piT_s23 (Or.inl hπ) s
    apply hι
    rw [map_mul, hs, ← hkq, ← hr, map_mul]
    group
  · obtain ⟨E, hE, hEq, hcard⟩ := hE16 q hq2 (Or.inl h)
    obtain ⟨E', hE', hE'l, hcard'⟩ := exists_elementary_of_conj_extremal hι hS hext hql E hE hEq
    have h8 := card_le_eight_of_le_centralizer hn (g := l) (by rw [hπ]) E' hE' hE'l
    omega
  · obtain ⟨E, hE, hEq, hcard⟩ := hE16 q hq2 (Or.inr h)
    obtain ⟨E', hE', hE'l, hcard'⟩ := exists_elementary_of_conj_extremal hι hS hext hql E hE hEq
    have h8 := card_le_eight_of_le_centralizer hn (g := l) (by rw [hπ]) E' hE' hE'l
    omega

theorem conj_mul_w1T_zT_of_conj_w1T (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega))) {l : L4Model n}
    (hl2 : l * l = 1) (hπ : piT l = s23)
    (hM8 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {l} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → w1T hn ∈ B)
    {g : G} (hg : g * ι l * g⁻¹ = ι (w1T hn)) :
    ∃ g' : G, g' * ι (l * w1T hn) * g'⁻¹ = ι (zT (by omega)) := by
  obtain ⟨k, hkl, hk⟩ := GHarris.exists_conj_extremal (S := ι.range) hS.isPGroup
    (isSylowOf_w1T hn hι hS) (u := ι l) (h := g) (by rw [← hg]; group)
  have hcar : ∀ c ∈ centralizer {l}, ∃ d ∈ centralizer {w1T hn}, ι d = k⁻¹ * ι c * k := by
    intro c hc
    have hcl : ι c ∈ (ι.range ⊓ centralizer {ι l} : Subgroup G) := by
      refine Subgroup.mem_inf.2 ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hc]
    obtain ⟨⟨d, hd⟩, hdc⟩ := Subgroup.mem_inf.1 (hk _ hcl)
    refine ⟨d, ?_, hd⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul, hd]
    exact Subgroup.mem_centralizer_singleton_iff.1 hdc
  set φ : L4Model n →* G := (MulAut.conj k⁻¹).toMonoidHom.comp ι with hφdef
  have hφ : ∀ x, φ x = k⁻¹ * ι x * k := fun x => by simp [φ]
  have hφinj : Function.Injective φ := fun x y h => hι (by rw [hφ, hφ] at h; simpa using h)
  have hle : (centralizer {l}).map φ ≤ ι.range := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨d, -, hd⟩ := hcar c hc
    exact ⟨d, by rw [hd, hφ]⟩
  set H := ((centralizer {l}).map φ).comap ι with hHdef
  have hHcard : Nat.card H = 2 ^ (2 * n) := by
    rw [← Subgroup.card_map_of_injective hι, hHdef, Subgroup.map_comap_eq_self hle,
      Subgroup.card_map_of_injective hφinj, card_centralizer_of_piT_s23 hn hl2 (Or.inl hπ)]
  have hHmem : ∀ d ∈ H, ∃ c ∈ centralizer {l}, ι d = k⁻¹ * ι c * k := by
    intro d hd
    obtain ⟨c, hc, hcd⟩ := Subgroup.mem_comap.1 hd
    exact ⟨c, hc, by rw [← hcd, hφ]⟩
  have hHw : H ≤ centralizer {w1T hn} := by
    intro d hd
    obtain ⟨c, hc, hcd⟩ := hHmem d hd
    obtain ⟨d', hd', hd'c⟩ := hcar c hc
    rwa [hι (hcd.trans hd'c.symm)]
  have hHA : 2 ^ (2 * n - 1) ≤ Nat.card (H ⊓ A n : Subgroup (L4Model n)) := by
    have h1 := card_eq_card_inf_A_mul H
    have h2 : Nat.card (H.map piT) ≤ 2 := by
      have : H.map piT ≤ V23 := by
        rw [Subgroup.map_le_iff_le_comap, ← centralizer_w1T hn]
        exact hHw
      exact (Subgroup.card_le_of_le this).trans card_V23.le
    have h3 : 2 ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hHcard, h3] at h1
    have h4 : 2 ^ (2 * n - 1) * 2 ≤ Nat.card (H ⊓ A n : Subgroup (L4Model n)) * 2 := by
      rw [h1]
      exact Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)
  set ψ : L4Model n →* G := (MulAut.conj k).toMonoidHom.comp ι with hψdef
  have hψ : ∀ x, ψ x = k * ι x * k⁻¹ := fun x => by simp [ψ]
  have hψinj : Function.Injective ψ := fun x y h => hι (by rw [hψ, hψ] at h; simpa using h)
  have hle' : (H ⊓ A n).map ψ ≤ ι.range := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨c, -, hcd⟩ := hHmem d (Subgroup.mem_inf.1 hd).1
    exact ⟨c, by rw [hψ, hcd]; group⟩
  set B := ((H ⊓ A n).map ψ).comap ι with hBdef
  have hBmem : ∀ b ∈ B, ∃ d ∈ H ⊓ A n, ι b = k * ι d * k⁻¹ := by
    intro b hb
    obtain ⟨d, hd, hdb⟩ := Subgroup.mem_comap.1 hb
    exact ⟨d, hd, by rw [← hdb, hψ]⟩
  have hBl : B ≤ centralizer {l} := by
    intro b hb
    obtain ⟨d, hd, hbd⟩ := hBmem b hb
    obtain ⟨c, hc, hcd⟩ := hHmem d (Subgroup.mem_inf.1 hd).1
    have : ι b = ι c := by rw [hbd, hcd]; group
    rwa [hι this]
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hd, had⟩ := hBmem a ha
    obtain ⟨d', hd', hbd'⟩ := hBmem b hb
    apply hι
    rw [map_mul, map_mul, had, hbd']
    have hc := A_comm (Subgroup.mem_inf.1 hd).2 (Subgroup.mem_inf.1 hd').2
    calc k * ι d * k⁻¹ * (k * ι d' * k⁻¹) = k * ι (d * d') * k⁻¹ := by rw [map_mul]; group
      _ = k * ι (d' * d) * k⁻¹ := by rw [hc]
      _ = k * ι d' * k⁻¹ * (k * ι d * k⁻¹) := by rw [map_mul]; group
  have hBcard : 2 ^ (2 * n - 1) ≤ Nat.card B := by
    rw [← Subgroup.card_map_of_injective hι, hBdef, Subgroup.map_comap_eq_self hle',
      Subgroup.card_map_of_injective hψinj]
    exact hHA
  obtain ⟨d₀, hd₀, hwd⟩ := hBmem _ (hM8 B hBl hBc hBcard)
  have hkw : k⁻¹ * ι (w1T hn) * k = ι d₀ := by rw [hwd]; group
  have hd₀A := (Subgroup.mem_inf.1 hd₀).2
  have hkw' : k⁻¹ * ι (w1T hn) * k⁻¹⁻¹ = ι d₀ := by rw [inv_inv, hkw]
  have hd₀2 := mul_self_of_conj_eq hι (w1T_mul_self hn) hkw'
  have hd₀1 := ne_one_of_conj_eq hι (w1T_ne_one hn) hkw'
  have hd₀w : d₀ ≠ w1T hn := by
    rintro rfl
    have h1 : k⁻¹ * ι l * k = k⁻¹ * ι (w1T hn) * k := by rw [hkl, hkw]
    have h2 : l = w1T hn := hι (by simpa using h1)
    rw [h2, mem_A_iff.1 (w1T_mem_A hn)] at hπ
    exact absurd hπ (by decide)
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hd₀A hd₀2
  have hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hp | hp
    · exfalso
      have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
          q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
        decide
      rcases key p hp with rfl | rfl | rfl | rfl
      · exact hd₀1 (omegaEl_zero hn)
      · exact not_conj_w1T_zT hn hι hS k⁻¹ (by rw [hkw', ← zT_eq_omegaEl hn])
      · exact not_conj_w1T_x1T hn hι hS k⁻¹ (by rw [hkw', ← x1T_eq_omegaEl hn])
      · obtain ⟨g', hg'⟩ := exists_conj_of_conj_isConj (g := k⁻¹) (b := y1T (n := n) (by omega))
          (by rw [hkw', ← y1T_eq_omegaEl hn]) (isConj_y1T_x1T (by omega))
        exact not_conj_w1T_x1T hn hι hS g' hg'
    · exact hp
  have hlw : k⁻¹ * ι (l * w1T hn) * k⁻¹⁻¹ = ι (w1T hn * omegaEl hn p) := by
    calc k⁻¹ * ι (l * w1T hn) * k⁻¹⁻¹ = (k⁻¹ * ι l * k) * (k⁻¹ * ι (w1T hn) * k) := by
          rw [map_mul]
          group
      _ = ι (w1T hn) * ι (omegaEl hn p) := by rw [hkl, hkw]
      _ = ι (w1T hn * omegaEl hn p) := (map_mul _ _ _).symm
  rcases w1T_mul_omegaEl_odd hn p hp with h | h | h | h
  · exfalso
    apply hd₀w
    calc omegaEl hn p = (w1T hn)⁻¹ * (w1T hn * omegaEl hn p) := by group
      _ = w1T hn := by rw [h, mul_one, inv_eq_of_mul_eq_one_right (w1T_mul_self hn)]
  · exact ⟨k⁻¹, by rw [hlw, h]⟩
  · obtain ⟨g₁, hg₁⟩ := hzx
    exact exists_conj_trans (g := k⁻¹) (b := x1T (n := n) (by omega)) (by rw [hlw, h]) hg₁
  · obtain ⟨g₁, hg₁⟩ := exists_conj_y1T_zT (by omega) hzx
    exact exists_conj_trans (g := k⁻¹) (b := y1T (n := n) (by omega)) (by rw [hlw, h]) hg₁

theorem exists_conj_zT_x1T_of_piT_s23 (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤) {l : L4Model n}
    (hπ : piT l = s23) {g : G} (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    ∃ k : G, k⁻¹ * ι l * k = ι (zT (by omega)) ∧
      (∀ c ∈ centralizer {l}, ∃ d : L4Model n, ι d = k⁻¹ * ι c * k) ∧
      k⁻¹ * ι (zT (by omega)) * k = ι (x1T (by omega)) := by
  have hlA : l ∉ A n := not_mem_A_of_piT_ne (by rw [hπ]; decide)
  obtain ⟨k, hkl, hk⟩ := exists_conj_zT_of_conj hn hS hg
  obtain ⟨e, he⟩ := hk _ (zT_mem_centralizer (by omega) l)
  obtain ⟨c, hc, hc4⟩ := exists_pow_four_eq_zT_of_piT_s23 hn (Or.inl hπ)
  obtain ⟨d, hd⟩ := hk c hc
  have hed : e = d ^ 4 :=
    hι (by rw [map_pow, hd, he, ← hc4, map_pow, GHarris.conj_pow_inv])
  have heA : e ∈ A n := hed ▸ pow_four_mem_A d
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  have he' : k⁻¹ * ι (zT (n := n) (by omega)) * k⁻¹⁻¹ = ι e := by rw [inv_inv, he]
  have he2 := mul_self_of_conj_eq hι hz2 he'
  have hz1 : zT (n := n) (by omega) ≠ 1 := fun h => by
    have := orderOf_zT (n := n) (by omega)
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have he1 := ne_one_of_conj_eq hι hz1 he'
  have hzc : ∀ a : L4Model n, a⁻¹ * zT (by omega) * a = zT (by omega) := fun a => by
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 (zT_mem_center (n := n) (by omega)) a,
      ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn heA he2
  rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hp | hp
  · have key : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
        q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
      decide
    rcases key p hp with rfl | rfl | rfl | rfl
    · exact absurd (omegaEl_zero hn) he1
    ·
      exfalso
      apply hlA
      have h1 : ι l = ι (zT (n := n) (by omega)) := by
        rw [← zT_eq_omegaEl hn] at he
        have h2 : k * ι (zT (n := n) (by omega)) * k⁻¹ = ι (zT (by omega)) := by
          calc k * ι (zT (n := n) (by omega)) * k⁻¹ =
              k * (k⁻¹ * ι (zT (by omega)) * k) * k⁻¹ := by rw [← he]
            _ = ι (zT (by omega)) := by group
        rw [← h2, ← hkl]
        group
      rw [hι h1]
      exact zT_mem_A _
    · exact ⟨k, hkl, hk, by rw [← he, x1T_eq_omegaEl hn]⟩
    ·
      refine ⟨k * ι (uT (by omega)), ?_, fun c hc => ?_, ?_⟩
      · calc (k * ι (uT (n := n) (by omega)))⁻¹ * ι l * (k * ι (uT (by omega))) =
            (ι (uT (by omega)))⁻¹ * (k⁻¹ * ι l * k) * ι (uT (by omega)) := by group
          _ = (ι (uT (by omega)))⁻¹ * ι (zT (by omega)) * ι (uT (by omega)) := by rw [hkl]
          _ = ι ((uT (by omega))⁻¹ * zT (by omega) * uT (by omega)) := by
            rw [map_mul, map_mul, map_inv]
          _ = ι (zT (by omega)) := by rw [hzc]
      · obtain ⟨d', hd'⟩ := hk c hc
        refine ⟨(uT (by omega))⁻¹ * d' * uT (by omega), ?_⟩
        rw [map_mul, map_mul, map_inv, hd']
        group
      · calc (k * ι (uT (n := n) (by omega)))⁻¹ * ι (zT (by omega)) * (k * ι (uT (by omega))) =
            (ι (uT (by omega)))⁻¹ * (k⁻¹ * ι (zT (by omega)) * k) * ι (uT (by omega)) := by
              group
          _ = (ι (uT (by omega)))⁻¹ * ι (y1T (by omega)) * ι (uT (by omega)) := by
            rw [← he, ← y1T_eq_omegaEl hn]
          _ = ι ((uT (by omega))⁻¹ * y1T (by omega) * uT (by omega)) := by
            rw [map_mul, map_mul, map_inv]
          _ = ι (x1T (by omega)) := by
            rw [← uT_conj_x1T (by omega)]
            group
  · exfalso
    obtain ⟨c', hc'⟩ := exists_conj_w1T_eq hn p hp
    apply not_conj_w1T_zT hn hι hS (k * ι c')
    rw [show k * ι c' * ι (w1T hn) * (k * ι c')⁻¹ = k * ι (c' * w1T hn * c'⁻¹) * k⁻¹ by
      rw [map_mul, map_mul, map_inv]; group, hc', he]
    group

theorem conj_of_conj_zT_of_piT_s23 (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hM7 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {x1T (by omega)} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → B ≤ A n)
    {l : L4Model n} (hl2 : l * l = 1) (hπ : piT l = s23) {g : G}
    (hg : g * ι l * g⁻¹ = ι (zT (by omega))) :
    (∃ g' : G, g' * ι (l * w1T hn) * g'⁻¹ = ι (w1T hn)) ∧
      ∃ g' : G, g' * ι (l * (tT (by omega) * l * (tT (by omega))⁻¹)) * g'⁻¹ =
        ι (zT (by omega)) := by
  obtain ⟨k, hkl, hk, hkz⟩ := exists_conj_zT_x1T_of_piT_s23 hn hι hS hπ hg
  have hcar : ∀ c ∈ centralizer {l}, ∃ d ∈ centralizer {x1T (n := n) (by omega)},
      ι d = k⁻¹ * ι c * k := by
    intro c hc
    obtain ⟨d, hd⟩ := hk c hc
    refine ⟨d, ?_, hd⟩
    rw [mem_centralizer_singleton_iff]
    apply hι
    have hcz : ι c * ι (zT (n := n) (by omega)) = ι (zT (by omega)) * ι c := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (zT_mem_center (by omega)) c]
    rw [map_mul, map_mul, hd, ← hkz]
    calc k⁻¹ * ι c * k * (k⁻¹ * ι (zT (by omega)) * k) =
        k⁻¹ * (ι c * ι (zT (by omega))) * k := by group
      _ = k⁻¹ * (ι (zT (by omega)) * ι c) * k := by rw [hcz]
      _ = k⁻¹ * ι (zT (by omega)) * k * (k⁻¹ * ι c * k) := by group
  set B : Subgroup (L4Model n) := centralizer {l} ⊓ V23.comap piT with hBdef
  set φ : L4Model n →* G := (MulAut.conj k⁻¹).toMonoidHom.comp ι with hφdef
  have hφ : ∀ x, φ x = k⁻¹ * ι x * k := fun x => by simp [φ]
  have hφinj : Function.Injective φ := fun x y h => hι (by rw [hφ, hφ] at h; simpa using h)
  have hle : B.map φ ≤ ι.range := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨d, -, hd⟩ := hcar c (Subgroup.mem_inf.1 hc).1
    exact ⟨d, by rw [hd, hφ]⟩
  set B' := (B.map φ).comap ι with hB'def
  have hB'mem : ∀ d ∈ B', ∃ c ∈ B, ι d = k⁻¹ * ι c * k := by
    intro d hd
    obtain ⟨c, hc, hcd⟩ := Subgroup.mem_comap.1 hd
    exact ⟨c, hc, by rw [← hcd, hφ]⟩
  have hB'x : B' ≤ centralizer {x1T (n := n) (by omega)} := by
    intro d hd
    obtain ⟨c, hc, hcd⟩ := hB'mem d hd
    obtain ⟨d', hd', hd'c⟩ := hcar c (Subgroup.mem_inf.1 hc).1
    rwa [hι (hcd.trans hd'c.symm)]
  have hB'c : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    obtain ⟨c, hc, hac⟩ := hB'mem a ha
    obtain ⟨c', hc', hbc'⟩ := hB'mem b hb
    apply hι
    rw [map_mul, map_mul, hac, hbc']
    have hcc := comm_of_mem_centralizer_inf_V23 hl2 hπ hc hc'
    calc k⁻¹ * ι c * k * (k⁻¹ * ι c' * k) = k⁻¹ * ι (c * c') * k := by rw [map_mul]; group
      _ = k⁻¹ * ι (c' * c) * k := by rw [hcc]
      _ = k⁻¹ * ι c' * k * (k⁻¹ * ι c * k) := by rw [map_mul]; group
  have hB'card : 2 ^ (2 * n - 1) ≤ Nat.card B' := by
    rw [← Subgroup.card_map_of_injective hι, hB'def, Subgroup.map_comap_eq_self hle,
      Subgroup.card_map_of_injective hφinj]
    exact le_card_centralizer_inf_V23 (by omega) hπ
  have hBA : ∀ c ∈ B, ∃ d ∈ A n, ι d = k⁻¹ * ι c * k := by
    intro c hc
    have hc' : φ c ∈ B.map φ := ⟨c, hc, rfl⟩
    obtain ⟨d, hd⟩ := hle hc'
    have hdB' : d ∈ B' := Subgroup.mem_comap.2 (by rw [hd]; exact hc')
    exact ⟨d, hM7 B' hB'x hB'c hB'card hdB', by rw [hd, hφ]⟩
  have hz2 : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT (by omega)]
  constructor
  ·
    obtain ⟨f, hfA, hf⟩ := hBA _ (w1T_mem_centralizer_inf_V23 hn hπ)
    have hf' : k⁻¹ * ι (w1T hn) * k⁻¹⁻¹ = ι f := by rw [inv_inv, hf]
    have hf2 := mul_self_of_conj_eq hι (w1T_mul_self hn) hf'
    have hf1 := ne_one_of_conj_eq hι (w1T_ne_one hn) hf'
    have hfz : f ≠ zT (by omega) := fun h => not_conj_w1T_zT hn hι hS k⁻¹ (by rw [hf', h])
    have hfx : f ≠ x1T (by omega) := fun h => not_conj_w1T_x1T hn hι hS k⁻¹ (by rw [hf', h])
    have hfy : f ≠ y1T (by omega) := fun h => by
      obtain ⟨g', hg'⟩ := exists_conj_of_conj_isConj (g := k⁻¹) (b := y1T (n := n) (by omega))
        (by rw [hf', h]) (isConj_y1T_x1T (by omega))
      exact not_conj_w1T_x1T hn hι hS g' hg'
    have hzfA : zT (by omega) * f ∈ A n := mul_mem (zT_mem_A _) hfA
    have hfc := Subgroup.mem_center_iff.1 (zT_mem_center (n := n) (by omega)) f
    have hzf2 : zT (n := n) (by omega) * f * (zT (by omega) * f) = 1 := by
      calc zT (n := n) (by omega) * f * (zT (by omega) * f) =
          zT (by omega) * (f * zT (by omega)) * f := by group
        _ = zT (by omega) * (zT (by omega) * f) * f := by rw [hfc]
        _ = zT (by omega) * zT (by omega) * (f * f) := by group
        _ = 1 := by rw [hz2, hf2, one_mul]
    obtain ⟨p, hp⟩ := exists_eq_omegaEl hn hzfA hzf2
    have hfp : f = zT (by omega) * omegaEl hn p := by
      rw [← hp, ← mul_assoc, hz2, one_mul]
    have hpodd : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (pat p 0 + pat p 1 + pat p 2 + pat p 3) with hq | hq
      · exfalso
        have key : ∀ q : Fin 2 × Fin 2 × Fin 2,
            (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 0 →
            q = (0, 0, 0) ∨ q = (0, 1, 1) ∨ q = (1, 0, 1) ∨ q = (1, 1, 0) := by
          decide
        rcases key p hq with rfl | rfl | rfl | rfl
        · exact hfz (by rw [hfp, omegaEl_zero, mul_one])
        · exact hf1 (by rw [hfp, ← zT_eq_omegaEl hn, hz2])
        · exact hfy (by rw [hfp, ← x1T_eq_omegaEl hn, zT_mul_x1T (by omega)])
        · exact hfx (by rw [hfp, ← y1T_eq_omegaEl hn, zT_mul_y1T (by omega)])
      · exact hq
    obtain ⟨c, hc⟩ := exists_conj_w1T_eq hn p hpodd
    have h1 : k⁻¹ * ι (l * w1T hn) * k⁻¹⁻¹ = ι (omegaEl hn p) := by
      rw [← hp, inv_inv, map_mul, map_mul, ← hkl, hf]
      group
    exact exists_conj_of_conj_isConj h1 (isConj_iff.2 ⟨c, hc⟩).symm
  ·
    obtain ⟨v, hvdef⟩ : ∃ v, v = tT (n := n) (by omega) * l * (tT (by omega))⁻¹ := ⟨_, rfl⟩
    rw [← hvdef]
    have hvl : v ∈ centralizer {l} := hvdef ▸ tT_conj_mem_centralizer_of_piT_s23 (by omega) hl2 hπ
    have hvπ : piT v = s01 := hvdef ▸ piT_tT_conj_of_piT_s23 (by omega) hπ
    have hv2 : v * v = 1 := hvdef ▸ conj_mul_self hl2
    obtain ⟨fv, hfv⟩ := hk v hvl
    obtain ⟨fw, hfwA, hfw⟩ := hBA _ (wT_mem_centralizer_inf_V23 (by omega) hπ)
    have hfvA : fv ∉ A n := by
      intro hfvA
      apply wT_not_mem_centralizer_of_piT_s01 hn hvπ
      rw [mem_centralizer_singleton_iff]
      have h := A_comm hfwA hfvA
      apply hι
      have e1 : ι (wT n) = k * ι fw * k⁻¹ := by rw [hfw]; group
      have e2 : ι v = k * ι fv * k⁻¹ := by rw [hfv]; group
      rw [map_mul, map_mul, e1, e2]
      calc k * ι fw * k⁻¹ * (k * ι fv * k⁻¹) = k * ι (fw * fv) * k⁻¹ := by rw [map_mul]; group
        _ = k * ι (fv * fw) * k⁻¹ := by rw [h]
        _ = k * ι fv * k⁻¹ * (k * ι fw * k⁻¹) := by rw [map_mul]; group
    have hfv' : k⁻¹ * ι v * k⁻¹⁻¹ = ι fv := by rw [inv_inv, hfv]
    have hfv2 := mul_self_of_conj_eq hι hv2 hfv'
    have hlv : ι l * ι v = ι v * ι l := by
      rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 hvl)]
    have h1 : k⁻¹ * ι (l * v) * k⁻¹⁻¹ = ι (fv * zT (by omega)) := by
      rw [inv_inv, map_mul, map_mul, ← hkl, hfv, hlv]
      group
    obtain ⟨g₁, hg₁⟩ := exists_conj_of_conj_isConj h1 (isConj_mul_zT hn hfvA hfv2)
    obtain ⟨g₂, hg₂⟩ := exists_conj_trans hg₁ (by rw [hfv]; group : k * ι fv * k⁻¹ = ι v)
    have h3 : IsConj v l := isConj_iff.2 ⟨(tT (n := n) (by omega))⁻¹, by rw [hvdef]; group⟩
    obtain ⟨g₃, hg₃⟩ := exists_conj_of_conj_isConj hg₂ h3
    exact exists_conj_trans hg₃ hg

theorem conj_zT_of_piT_zP_of_conj (hn : 3 ≤ n) {ι : L4Model n →* G}
    (hι : Function.Injective ι) (hS : IsSylowOf 2 ι.range ⊤)
    (hM7 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {x1T (by omega)} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → B ≤ A n)
    {l : L4Model n} (hl2 : l * l = 1) (hπ : piT l = s23) {g : G}
    (hg : g * ι l * g⁻¹ = ι (zT (by omega))) {μ : L4Model n} (hμ2 : μ * μ = 1)
    (hμ : piT μ = zP) : ∃ g' : G, g' * ι μ * g'⁻¹ = ι (zT (by omega)) := by
  obtain ⟨v, hvdef⟩ : ∃ v, v = tT (n := n) (by omega) * l * (tT (by omega))⁻¹ := ⟨_, rfl⟩
  have hvl : v ∈ centralizer {l} := hvdef ▸ tT_conj_mem_centralizer_of_piT_s23 (by omega) hl2 hπ
  have hvπ : piT v = s01 := hvdef ▸ piT_tT_conj_of_piT_s23 (by omega) hπ
  have hv2 : v * v = 1 := hvdef ▸ conj_mul_self hl2
  have hlv := mem_centralizer_singleton_iff.1 hvl
  have hμ₀2 : l * v * (l * v) = 1 := by
    calc l * v * (l * v) = l * (v * l) * v := by group
      _ = l * (l * v) * v := by rw [hlv]
      _ = l * l * (v * v) := by group
      _ = 1 := by rw [hl2, hv2, one_mul]
  have hμ₀π : piT (l * v) = zP := by
    rw [map_mul, hπ, hvπ]
    decide
  obtain ⟨g₀, hg₀⟩ := (conj_of_conj_zT_of_piT_s23 hn hι hS hM7 hl2 hπ hg).2
  rw [← hvdef] at hg₀
  set ι' : L4Model n →* G := ι.comp (diagAut n).toMonoidHom with hι'def
  have hι' : Function.Injective ι' := hι.comp (diagAut n).injective
  have hS' : IsSylowOf 2 ι'.range ⊤ := by
    rw [hι'def, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective (diagAut n).toMonoidHom (diagAut n).surjective,
      ← MonoidHom.range_eq_map]
    exact hS
  have hι'app : ∀ x, ι' x = ι (diagAut n x) := fun x => rfl
  have hzA : diagAut n (zT (n := n) (by omega)) = zT (by omega) := diagAut_of_mem_A (zT_mem_A _)
  have hg' : ∃ g' : G, g' * ι' l * g'⁻¹ = ι' (zT (by omega)) := by
    rw [hι'app, hι'app, hzA]
    exact exists_conj_of_isConj (isConj_diagAut_of_piT_s23 hn hl2 hπ) hg
  obtain ⟨g'', hg''⟩ := hg'
  obtain ⟨g₁, hg₁⟩ := (conj_of_conj_zT_of_piT_s23 hn hι' hS' hM7 hl2 hπ hg'').2
  rw [← hvdef, hι'app, hι'app, hzA] at hg₁
  have key : (∃ g' : G, g' * ι (uvT (by omega)) * g'⁻¹ = ι (zT (by omega))) ∧
      ∃ g' : G, g' * ι (uvxyT (by omega)) * g'⁻¹ = ι (zT (by omega)) := by
    rcases isConj_diagAut_of_piT_zP hn hμ₀2 hμ₀π with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨exists_conj_of_isConj h1.symm hg₀, exists_conj_of_isConj h2.symm hg₁⟩
    · exact ⟨exists_conj_of_isConj h2.symm hg₁, exists_conj_of_isConj h1.symm hg₀⟩
  obtain ⟨⟨g₂, hg₂⟩, ⟨g₃, hg₃⟩⟩ := key
  rcases isConj_uvT_or_uvxyT hn hμ2 hμ with h | h
  · exact exists_conj_of_isConj h hg₂
  · exact exists_conj_of_isConj h hg₃

theorem lemma36 (hn : 3 ≤ n) {ι : L4Model n →* G} (hι : Function.Injective ι)
    (hS : IsSylowOf 2 ι.range ⊤)
    (hzx : ∃ g : G, g * ι (x1T (by omega)) * g⁻¹ = ι (zT (by omega)))
    (hsqrt : ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP → ∃ r : L4Model n, r * r = μ)
    (hE16 : ∀ μ : L4Model n, μ * μ = 1 → (piT μ = tP ∨ piT μ = tzP) →
      ∃ E : Subgroup (L4Model n), (∀ x ∈ E, x * x = 1) ∧ E ≤ centralizer {μ} ∧
        Nat.card E = 16)
    (hM7 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {x1T (by omega)} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → B ≤ A n)
    (hM8 : ∀ B : Subgroup (L4Model n), B ≤ centralizer {uT (by omega)} →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → 2 ^ (2 * n - 1) ≤ Nat.card B → w1T hn ∈ B)
    (hu : ι (uT (by omega)) ∈ commutator G) :
    (((∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (w1T hn)) ∨
      ((∃ g : G, g * ι (uw1T hn) * g⁻¹ = ι (zT (by omega))) ∧
        ∃ g : G, g * ι (uT (by omega)) * g⁻¹ = ι (w1T hn))) ∧
    ∀ μ : L4Model n, μ * μ = 1 → piT μ = zP →
      ∃ g : G, g * ι μ * g⁻¹ = ι (zT (by omega)) := by
  have hu2 := uT_mul_self (n := n) (by omega)
  have hπu : piT (uT (n := n) (by omega)) = s23 := piT_uT _
  have huw := uT_mul_w1T (n := n) hn
  rcases conj_zT_or_w1T_of_piT_s23 hn hι hS hzx hsqrt hE16 hu2 hπu hu with ⟨g, hg⟩ | ⟨g, hg⟩
  · have h := (conj_of_conj_zT_of_piT_s23 hn hι hS hM7 hu2 hπu hg).1
    rw [huw] at h
    exact ⟨Or.inl ⟨⟨g, hg⟩, h⟩,
      fun μ hμ2 hμ => conj_zT_of_piT_zP_of_conj hn hι hS hM7 hu2 hπu hg hμ2 hμ⟩
  · have h := conj_mul_w1T_zT_of_conj_w1T hn hι hS hzx hu2 hπu hM8 hg
    rw [huw] at h
    obtain ⟨g', hg'⟩ := h
    exact ⟨Or.inr ⟨⟨g', hg'⟩, ⟨g, hg⟩⟩,
      fun μ hμ2 hμ => conj_zT_of_piT_zP_of_conj hn hι hS hM7 (uw1T_mul_self hn) rfl hg' hμ2 hμ⟩

end CFSG.LocalAnalysis.Mason73
