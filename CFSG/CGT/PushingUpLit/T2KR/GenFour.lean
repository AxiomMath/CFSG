module

public import CFSG.CGT.PushingUpLit.T2KR.GenFourMod
public import CFSG.CGT.PushingUpLit.T2KR.Count1
public import CFSG.CGT.PushingUpLit.T2KR.GenFourGrp

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem conj_mem_LQ {m x : G} (hm : m ∈ M) (hx : x ∈ L ⊔ QM L M) :
    m * x * m⁻¹ ∈ L ⊔ QM L M := by
  obtain ⟨l, hl, q, hq, rfl⟩ := H.mem_LQ_iff.1 hx
  have hL : m * l * m⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (H.normal hm) l).1 hl
  have hQ : m * q * m⁻¹ ∈ QM L M :=
    (Subgroup.mem_normalizer_iff.1 (NatBlock.le_normalizer_centralizer H.normal hm) q).1 hq
  have e : m * (l * q) * m⁻¹ = (m * l * m⁻¹) * (m * q * m⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hL hQ

include H in
theorem mem_Q_iff_conj {m x : G} (hm : m ∈ M) : m * x * m⁻¹ ∈ QM L M ↔ x ∈ QM L M := by
  have h : ∀ {m x : G}, m ∈ M → x ∈ QM L M → m * x * m⁻¹ ∈ QM L M := fun hm hx =>
    (Subgroup.mem_normalizer_iff.1 (NatBlock.le_normalizer_centralizer H.normal hm) _).1 hx
  refine ⟨fun hx => ?_, h hm⟩
  have := h (M.inv_mem hm) hx
  simpa [mul_assoc] using this

include H in
theorem exists_two_gens_mod_Q (hn : n = 2) {S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup 2 S) :
    ∃ s : Finset G, s.card ≤ 2 ∧ (↑s : Set G) ⊆ (S : Set G) ∧
      S ≤ Subgroup.closure (s : Set G) ⊔ (S ⊓ QM L M) := by
  classical
  set N : Subgroup G := S ⊓ (L ⊔ QM L M) with hNdef
  have hNS : N ≤ S := inf_le_left
  have hNLQ : N ≤ L ⊔ QM L M := inf_le_right
  have hN2 : IsPGroup 2 N := hS.to_le hNS
  have hQN : N ⊓ QM L M = S ⊓ QM L M := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxS, _⟩, hxQ⟩
      exact ⟨hxS, hxQ⟩
    · rintro ⟨hxS, hxQ⟩
      exact ⟨⟨hxS, (le_sup_right : QM L M ≤ L ⊔ QM L M) hxQ⟩, hxQ⟩
  have hidx : N.relIndex S ≤ 2 := by
    have := H.relIndex_le_card_aut hSM hS
    rwa [hn] at this
  obtain ⟨p, hp⟩ := H.exists_root_point_of_isPGroup N hNLQ hN2
  have hF : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hroot : Nat.card (rootGrp p) = 4 := by rw [card_rootGrp, hF]
  have hrange : Nat.card (H.rhoOn N hNLQ).range ≤ 4 :=
    (Subgroup.card_le_of_le hp).trans (le_of_eq hroot)
  have hrel : (N ⊓ QM L M).relIndex N ≤ 2 ^ 2 := by
    rw [H.relIndex_eq_card_range N hNLQ]
    simpa using hrange
  by_cases hSN : S ≤ N
  · obtain ⟨t, htc, htN, ht⟩ := exists_finset_closure_sup_eq_of_relIndex_le 2 (N ⊓ QM L M)
      inf_le_left hrel
    refine ⟨t, htc, fun x hx => hNS (htN hx), ?_⟩
    calc S ≤ N := hSN
      _ = Subgroup.closure (t : Set G) ⊔ (N ⊓ QM L M) := ht.symm
      _ = Subgroup.closure (t : Set G) ⊔ (S ⊓ QM L M) := by rw [hQN]
  · obtain ⟨b, hbS, hbN⟩ := Set.not_subset.1 hSN
    have hbM : b ∈ M := hSM hbS
    have hN2' : N.relIndex S = 2 := by
      have hne : N.relIndex S ≠ 1 := fun h => hbN (Subgroup.relIndex_eq_one.1 h hbS)
      have hpos := relIndex_pos_of_finite N S
      omega
    have hbχ : H.chi ⟨b, hbM⟩ ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := hS ⟨b, hbS⟩
      have hk' : (⟨b, hbM⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg (fun z : ↥S => (z : G)) hk
        simpa using this)
      exact hbN ⟨hbS, H.mem_LQ_of_chi_eq_one hk' h1⟩
    have hcos : ∀ x ∈ S, x ∈ N ∨ b⁻¹ * x ∈ N := by
      intro x hx
      by_cases hxN : x ∈ N
      · exact Or.inl hxN
      · exact Or.inr (inv_mul_mem_of_relIndex_two hN2' hbS hx hbN hxN)
    have hred : ∀ C : Subgroup G, b ∈ C → N ≤ C ⊔ (S ⊓ QM L M) → S ≤ C ⊔ (S ⊓ QM L M) := by
      intro C hbC hNC x hx
      rcases hcos x hx with h | h
      · exact hNC h
      · have e : x = b * (b⁻¹ * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ ((le_sup_left : C ≤ C ⊔ (S ⊓ QM L M)) hbC) (hNC h)
    by_cases hrel2 : (N ⊓ QM L M).relIndex N ≤ 2
    · obtain ⟨t, htc, htN, ht⟩ := exists_finset_closure_sup_eq_of_relIndex_le 1 (N ⊓ QM L M)
        inf_le_left (by simpa using hrel2)
      have hsub : (↑(insert b t) : Set G) ⊆ (S : Set G) := by
        intro y hy
        rw [Finset.coe_insert] at hy
        rcases hy with rfl | hy
        · exact hbS
        · exact hNS (htN hy)
      refine ⟨insert b t, ?_, hsub, ?_⟩
      · calc (insert b t).card ≤ t.card + 1 := Finset.card_insert_le _ _
          _ ≤ 2 := by omega
      · refine hred _ (Subgroup.subset_closure (by simp)) ?_
        calc N = Subgroup.closure (t : Set G) ⊔ (N ⊓ QM L M) := ht.symm
          _ ≤ Subgroup.closure ((insert b t : Finset G) : Set G) ⊔ (S ⊓ QM L M) := by
            rw [hQN]
            exact sup_le_sup_right (Subgroup.closure_mono (by
              intro y hy; rw [Finset.coe_insert]; exact Or.inr hy)) _
    ·
      have hdvd : Nat.card (H.rhoOn N hNLQ).range ∣ 4 := by
        rw [← hroot]
        exact Subgroup.card_dvd_of_le hp
      have hrel4 : Nat.card (H.rhoOn N hNLQ).range = 4 := by
        have hr : (N ⊓ QM L M).relIndex N = Nat.card (H.rhoOn N hNLQ).range :=
          H.relIndex_eq_card_range N hNLQ
        have hpos : 0 < Nat.card (H.rhoOn N hNLQ).range := Nat.card_pos
        have h3 : 3 ≤ Nat.card (H.rhoOn N hNLQ).range := by omega
        have hle : Nat.card (H.rhoOn N hNLQ).range ≤ 4 := hrange
        have : Nat.card (H.rhoOn N hNLQ).range ∈ ({1, 2, 4} : Finset ℕ) := by
          have h4 : Nat.card (H.rhoOn N hNLQ).range ∣ 4 := hdvd
          have : Nat.card (H.rhoOn N hNLQ).range ∈ Nat.divisors 4 :=
            Nat.mem_divisors.2 ⟨h4, by norm_num⟩
          have e : Nat.divisors 4 = {1, 2, 4} := by decide
          rwa [e] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega
      have hrg : (H.rhoOn N hNLQ).range = rootGrp p :=
        Subgroup.eq_of_le_of_card_ge hp (by rw [hroot, hrel4])
      obtain ⟨x, hxN, hx⟩ := H.exists_actHom_conj_ne N hNLQ hbM hbχ p (fun g hg => by
        have : g ∈ (H.rhoOn N hNLQ).range := hrg ▸ hg
        obtain ⟨y, hy⟩ := this
        exact ⟨y, hy⟩)
      set m : G := b * x * b⁻¹ with hm
      have hxLQ : x ∈ L ⊔ QM L M := hNLQ hxN
      have hmLQ : m ∈ L ⊔ QM L M := H.conj_mem_LQ hbM hxLQ
      have hmN : m ∈ N := ⟨S.mul_mem (S.mul_mem hbS (hNS hxN)) (S.inv_mem hbS), hmLQ⟩
      have hxm : H.actHom ⟨m, H.LQ_le hmLQ⟩ ≠ H.actHom ⟨x, H.LQ_le hxLQ⟩ := by
        intro h
        apply hx
        have e : (⟨b, hbM⟩ * ⟨x, H.LQ_le (hNLQ hxN)⟩ * ⟨b, hbM⟩⁻¹ : ↥M) =
            ⟨m, H.LQ_le hmLQ⟩ := Subtype.ext rfl
        rw [e]
        exact h
      set f := H.rhoOn N hNLQ with hf
      have hfx : f ⟨x, hxN⟩ = H.rho ⟨x, hxLQ⟩ := rfl
      have hfm : f ⟨m, hmN⟩ = H.rho ⟨m, hmLQ⟩ := rfl
      have hfxm : f ⟨x, hxN⟩ ≠ f ⟨m, hmN⟩ := by
        intro h
        apply hxm
        rw [hfx, hfm] at h
        have h1 := congrArg (slPerm (Fq n)) h
        rw [H.slPerm_rho, H.slPerm_rho] at h1
        exact h1.symm
      have hQiff : x ∈ QM L M ↔ m ∈ QM L M := (H.mem_Q_iff_conj hbM).symm
      have hfx1 : f ⟨x, hxN⟩ ≠ 1 := by
        intro h
        have hx1 : x ∈ QM L M := by
          rw [hfx] at h
          exact (H.rho_eq_one_iff _).1 h
        have hm1 : m ∈ QM L M := hQiff.1 hx1
        have hm' : f ⟨m, hmN⟩ = 1 := by
          rw [hfm]
          exact (H.rho_eq_one_iff _).2 hm1
        exact hfxm (h.trans hm'.symm)
      have hfm1 : f ⟨m, hmN⟩ ≠ 1 := by
        intro h
        have hm1 : m ∈ QM L M := by
          rw [hfm] at h
          exact (H.rho_eq_one_iff _).1 h
        have hx1 : x ∈ QM L M := hQiff.2 hm1
        have hx' : f ⟨x, hxN⟩ = 1 := by
          rw [hfx]
          exact (H.rho_eq_one_iff _).2 hx1
        exact hfxm (hx'.trans h.symm)
      have hgen := le_closure_pair_sup_map_ker f hrange hxN hmN hfx1 hfm1 hfxm
      have hker : f.ker.map N.subtype = N ⊓ QM L M := by
        rw [hf, H.rhoOn_ker, Subgroup.subgroupOf_map_subtype]
        exact inf_eq_left.2 inf_le_left
      rw [hker] at hgen
      have hsub : (↑({x, b} : Finset G) : Set G) ⊆ (S : Set G) := by
        intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact hNS hxN
        · exact hbS
      refine ⟨{x, b}, Finset.card_le_two, hsub, ?_⟩
      have hbC : b ∈ Subgroup.closure ((({x, b} : Finset G)) : Set G) :=
        Subgroup.subset_closure (by simp)
      have hxC : x ∈ Subgroup.closure ((({x, b} : Finset G)) : Set G) :=
        Subgroup.subset_closure (by simp)
      refine hred _ hbC ?_
      calc N ≤ Subgroup.closure ({x, m} : Set G) ⊔ (N ⊓ QM L M) := hgen
        _ ≤ Subgroup.closure ((({x, b} : Finset G)) : Set G) ⊔ (S ⊓ QM L M) := by
          rw [hQN]
          refine sup_le_sup_right ((Subgroup.closure_le _).2 ?_) _
          intro y hy
          rcases hy with rfl | hy
          · exact hxC
          · rw [Set.mem_singleton_iff] at hy
            rw [hy, hm]
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbC hxC) (Subgroup.inv_mem _ hbC)


include H in
theorem exists_card_le_four (hn : n = 2) (hQV : QM L M = blockU L) {S : Subgroup G}
    (hSM : S ≤ M) (hS : IsPGroup 2 S) :
    ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = S := by
  classical
  have hF : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hVcard : Nat.card ↥(blockU L) = 16 := by
    rw [H.card_V, hF]
    norm_num
  by_cases hSV : S ≤ blockU L
  · have hrel : (⊥ : Subgroup G).relIndex S ≤ 2 ^ 4 := by
      rw [Subgroup.relIndex_bot_left]
      have := Subgroup.card_le_of_le hSV
      omega
    obtain ⟨t, htc, htS, ht⟩ := exists_finset_closure_sup_eq_of_relIndex_le 4 ⊥ bot_le hrel
    exact ⟨t, htc, by simpa using ht⟩
  · obtain ⟨s₀, hs₀S, hs₀V⟩ := Set.not_subset.1 hSV
    set W : Subgroup G := S ⊓ QM L M with hW
    have hWS : W ≤ S := inf_le_left
    obtain ⟨s, hsc, hsS, hSs⟩ := H.exists_two_gens_mod_Q hn hSM hS
    have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => H.Q_comm a ha.2 b hb.2
    have hWn : ∀ x ∈ S, ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun x hx w hw =>
      ⟨S.mul_mem (S.mul_mem hx hw.1) (S.inv_mem hx), (H.mem_Q_iff_conj (hSM hx)).2 hw.2⟩
    have hs₀M : s₀ ∈ M := hSM hs₀S
    have hs₀Q : s₀ ∉ QM L M := by rw [hQV]; exact hs₀V
    have hfix : Nat.card {w : G // w ∈ W ∧ s₀ * w = w * s₀} ≤ 4 := by
      obtain ⟨k, hk⟩ := hS ⟨s₀, hs₀S⟩
      have hk' : s₀ ^ 2 ^ k = 1 := by simpa using congrArg (fun z : ↥S => (z : G)) hk
      have h1 := H.card_fixed_le_card hs₀M hk' hs₀Q
      rw [hF] at h1
      refine le_trans ?_ h1
      have hWV : ∀ w ∈ W, w ∈ blockU L := fun w hw => hQV ▸ hw.2
      refine Nat.card_le_card_of_injective
        (fun w : {w : G // w ∈ W ∧ s₀ * w = w * s₀} => (⟨H.D.ψe w.1, ?_⟩ :
          {w : Fin 2 → Fq n // H.actHom ⟨s₀, hs₀M⟩ w = w})) ?_
      · show H.act s₀ (H.D.ψe w.1) = H.D.ψe w.1
        unfold act
        rw [H.vec_ψe (hWV _ w.2.1)]
        have : s₀ * w.1 * s₀⁻¹ = w.1 := by
          rw [w.2.2]; group
        rw [this]
      · intro u v huv
        have h1 : H.D.ψe u.1 = H.D.ψe v.1 :=
          congrArg (fun z : {w : Fin 2 → Fq n // H.actHom ⟨s₀, hs₀M⟩ w = w} => z.1) huv
        exact Subtype.ext (H.ψe_injOn (hWV _ u.2.1) (hWV _ v.2.1) h1)
    obtain ⟨w₀, hw₀c, hw₀W, hw₀⟩ := exists_two_generators_mod_commutator (S := S) (W := W) hWc
      hWn hs₀S hfix
    refine ⟨s ∪ w₀, ?_, ?_⟩
    · calc (s ∪ w₀).card ≤ s.card + w₀.card := Finset.card_union_le _ _
        _ ≤ 4 := by omega
    · rw [Finset.coe_union]
      exact closure_union_eq hS hWS hsS (fun x hx => hWS (hw₀W hx)) hSs hw₀

end MData

end CFSG.CGT.PushingUpLit.T2KR
