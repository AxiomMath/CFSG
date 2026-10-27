module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.DihedralPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step2

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Setting

theorem z_ne_sq (H : Setting G) (y : G) : y * y ≠ H.z := by
  intro hy
  have hcomm : y * H.z = H.z * y := by
    calc y * H.z = y * (y * y) := by rw [hy]
      _ = (y * y) * y := by group
      _ = H.z * y := by rw [hy]
  have hC : y ∈ centralizer ({H.z} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  rcases H.mem_centralizer_iff.1 hC with hL | hL
  · exact H.z_not_mem_L (hy ▸ mul_mem hL hL)
  · refine H.z_not_mem_L ?_
    have e : y * H.z * (y * H.z) = H.z := by
      calc y * H.z * (y * H.z) = y * (H.z * y) * H.z := by group
        _ = y * (y * H.z) * H.z := by rw [hcomm]
        _ = (y * y) * (H.z * H.z) := by group
        _ = H.z := by rw [hy, H.z_mul_self, mul_one]
    exact e ▸ mul_mem hL hL

end Setting

theorem exists_index_two_avoiding {U A : Type*} [Group U] [Finite U] [Group A] [Finite A]
    (ρ : U →* A) (hρ : Nat.card ρ.range = 8) (hU : Nat.card U = 16) {a b c : U}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 4 = 1)
    (hgen : ρ.range ≤ closure {ρ a, ρ b}) (hc : ρ c = 1) (hc1 : c ≠ 1) :
    ∃ W : Subgroup U, W.index = 2 ∧ c ∉ W := by
  have hWcard : Nat.card (closure {a, b} : Subgroup U) ≤ 8 :=
    card_closure_le_of_dihedral ha hb hab
  set W : Subgroup U := closure {a, b} with hW
  have hmap : W.map ρ = closure {ρ a, ρ b} := by
    rw [hW, MonoidHom.map_closure, Set.image_pair]
  have h8 : 8 ≤ Nat.card (W.map ρ) := by
    rw [← hρ]
    exact card_le_of_le (hmap ▸ hgen)
  set f : W →* A := ρ.domRestrict W
  have hfk := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.domRestrict_range W ρ] at hfk
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  have hk1 : Nat.card f.ker = 1 := by nlinarith
  have hW8 : Nat.card W = 8 := by nlinarith
  refine ⟨W, ?_, fun hcW => hc1 ?_⟩
  · have := Subgroup.index_mul_card W
    rw [hW8, hU] at this
    omega
  · have hmem : (⟨c, hcW⟩ : W) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact hc
    rw [eq_bot_of_card_eq _ hk1] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)

theorem exists_index_two_avoiding_of_normal {T A : Type*} [Group T] [Finite T] [Group A]
    [Finite A] (ρ : T →* A) (N : Subgroup T) [N.Normal] (hN : N ≤ ρ.ker)
    (hρ : Nat.card ρ.range = 8) (hT : Nat.card T = 16 * Nat.card N) {a b c : T}
    (ha : a * a ∈ N) (hb : b * b ∈ N) (hab : (a * b) ^ 4 ∈ N)
    (hgen : ρ.range ≤ closure {ρ a, ρ b}) (hc : ρ c = 1) (hcN : c ∉ N) :
    ∃ M : Subgroup T, N ≤ M ∧ c ∉ M ∧ M.index = 2 := by
  set ρ' : T ⧸ N →* A := QuotientGroup.lift N ρ hN
  have hrange : ρ'.range = ρ.range := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H t => exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(t : T ⧸ N), rfl⟩
  have hU : Nat.card (T ⧸ N) = 16 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [hT] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  obtain ⟨W, hWi, hcW⟩ := exists_index_two_avoiding ρ' (a := (a : T ⧸ N)) (b := (b : T ⧸ N))
    (c := (c : T ⧸ N)) (by rw [hrange]; exact hρ) hU
    (by rw [← QuotientGroup.mk_mul]; exact (QuotientGroup.eq_one_iff _).2 ha)
    (by rw [← QuotientGroup.mk_mul]; exact (QuotientGroup.eq_one_iff _).2 hb)
    (by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 hab)
    (by rw [hrange]; exact hgen) hc (fun h => hcN ((QuotientGroup.eq_one_iff c).1 h))
  refine ⟨W.comap (QuotientGroup.mk' N), fun n hn => ?_, hcW, ?_⟩
  · show (n : T ⧸ N) ∈ W
    rw [(QuotientGroup.eq_one_iff n).2 hn]
    exact one_mem W
  · rw [Subgroup.index_comap_of_surjective W (QuotientGroup.mk'_surjective N)]
    exact hWi

namespace Stage

variable {H : Setting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem sq_mem_of_mem {y : G} (hy : y * y ∈ S) : y * y ∈ Λ := by
  by_contra hΛ
  obtain ⟨c, hc⟩ := _root_.isConj_iff.1 (h.conj _ hy hΛ)
  refine H.z_ne_sq (c⁻¹ * y * c) ?_
  calc c⁻¹ * y * c * (c⁻¹ * y * c) = c⁻¹ * (y * y) * c := by group
    _ = H.z := by rw [← hc]; group

include h in
theorem exists_M0 (_hS : 2 ∣ S.index) (hcase : Nat.card (H.RC S) = Nat.card S)
    {T : Subgroup G} (_hT : IsPGroup 2 T) (hST : S ≤ T) (hTN : T ≤ normalizer (S : Set G))
    (hTcard : Nat.card T = 8 * Nat.card S) :
    ∃ M₀ : Subgroup G, M₀ ≤ T ∧ Λ ≤ M₀ ∧ H.z ∉ M₀ ∧ M₀.relIndex T = 2 := by
  have hΛT : Λ ≤ T := h.le.trans hST
  have hzT : H.z ∈ T := hST h.z_mem
  have hTE : T ≤ normalizer (H.E : Set G) := fun t ht =>
    mem_normalizer_iff.2 fun e => ⟨fun he => h.N_conj_E (hTN ht) he, fun he => by
      have := h.N_conj_E (inv_mem (hTN ht)) he
      simpa [mul_assoc] using this⟩
  set ρ : T →* MulAut H.E := H.E.normalizerMonoidHom.comp (Subgroup.inclusion hTE)
  have hρapp : ∀ (t : T) (e : H.E), ((ρ t e : H.E) : G) = t * e * (t : G)⁻¹ := fun t e => rfl
  have hRC : H.RC S = S := (eq_of_le_of_card_ge h.S_le_RC hcase.le).symm
  have hker : ∀ t : T, ρ t = 1 ↔ (t : G) ∈ S := by
    intro t
    constructor
    · intro h1
      have hc : (t : G) ∈ centralizer (H.E : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
        have h2 := congrArg (fun φ : MulAut H.E => ((φ ⟨e, he⟩ : H.E) : G)) h1
        simp only [hρapp, MulAut.one_apply] at h2
        calc e * t = (t * e * (t : G)⁻¹) * t := by rw [h2]
          _ = t * e := by group
      have : (t : G) ∈ H.RC S := ⟨hc, hTN t.2⟩
      rwa [hRC] at this
    · intro hs
      have hc : (t : G) ∈ centralizer (H.E : Set G) := (h.S_le_RC hs).1
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hρapp]
      have := Subgroup.mem_centralizer_iff.1 hc e e.2
      show (t : G) * e * (t : G)⁻¹ = e
      rw [← this]
      group
  have hkercard : Nat.card ρ.ker = Nat.card S :=
    Nat.card_congr ⟨fun t => ⟨t.1.1, (hker t.1).1 t.2⟩,
      fun s => ⟨⟨s.1, hST s.2⟩, (hker ⟨s.1, hST s.2⟩).2 s.2⟩, fun t => rfl, fun s => rfl⟩
  have hrange : Nat.card ρ.range = 8 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hkercard, hTcard] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))
  have hEcomm : ∀ a b : H.E, a * b = b * a := fun a b => Subtype.ext (H.E_comm a.2 b.2)
  have hEsq : ∀ a : H.E, a * a = 1 := fun a => Subtype.ext (H.sq_E a a.2)
  obtain ⟨α, β, hαP, hβP, hα, hβ, hαβ, hgen⟩ :=
    exists_dihedral_pair H.card_E hEcomm hEsq hrange
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hαP
  obtain ⟨s', rfl⟩ := MonoidHom.mem_range.1 hβP
  have hsq : ∀ t : T, ρ t * ρ t = 1 → (t : G) * t ∈ Λ := fun t ht =>
    h.sq_mem_of_mem ((hker (t * t)).1 (by rw [map_mul]; exact ht))
  have h4 : (ρ s * ρ s') ^ 4 = 1 := hαβ ▸ pow_orderOf_eq_one _
  have hy : ρ ((s * s') ^ 2) * ρ ((s * s') ^ 2) = 1 := by
    rw [map_pow, ← pow_add, map_mul]
    exact h4
  have hab4 : (s * s') ^ 4 ∈ Λ.subgroupOf T := by
    have : (s * s') ^ 4 = (s * s') ^ 2 * (s * s') ^ 2 := by rw [← pow_add]
    rw [this]
    exact hsq _ hy
  have : (Λ.subgroupOf T).Normal := ⟨fun n hn g => h.N_normalizes_Λ (hTN g.2) hn⟩
  have hN : Λ.subgroupOf T ≤ ρ.ker := fun n hn => (hker n).2 (h.le hn)
  have hNcard : Nat.card (Λ.subgroupOf T) = Nat.card Λ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛT).toEquiv
  have hTc : Nat.card T = 16 * Nat.card (Λ.subgroupOf T) := by
    rw [hTcard, hNcard, h.card_S]
    ring
  obtain ⟨M, hNM, hzM, hMi⟩ := exists_index_two_avoiding_of_normal ρ (Λ.subgroupOf T) hN hrange
    hTc (a := s) (b := s') (c := ⟨H.z, hzT⟩) (hsq s hα) (hsq s' hβ) hab4 hgen
    ((hker _).2 h.z_mem) (fun hzN => h.z_not_mem hzN)
  refine ⟨M.map T.subtype, Subgroup.map_subtype_le M, fun l hl => ?_, ?_, ?_⟩
  · exact ⟨⟨l, hΛT hl⟩, hNM hl, rfl⟩
  · rintro ⟨t, htM, hteq⟩
    exact hzM (by
      have : t = ⟨H.z, hzT⟩ := Subtype.ext hteq
      rwa [this] at htM)
  · have : (M.map T.subtype).relIndex T = M.index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        comap_map_eq_self_of_injective T.subtype_injective]
    rw [this, hMi]

end Stage

end CFSG.EvenSporadicStandard.J1Std
