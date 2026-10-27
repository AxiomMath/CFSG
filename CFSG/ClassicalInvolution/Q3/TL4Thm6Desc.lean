module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Thm6

section Lift

variable {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal] {R : Subgroup Y}
  {S : Sylow 2 R} {t : Y}

omit [Finite Y] [N.Normal] in
theorem card_conjSub (g : Y) (H : Subgroup Y) : Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [Finite Y] in
theorem conjSub_inf_eq_bot {H : Subgroup Y} (hH : H ⊓ N = ⊥) (g : Y) : conjSub g H ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxN⟩ := Subgroup.mem_inf.mp hx
  have h1 : g⁻¹ * x * g ∈ H ⊓ N :=
    ⟨mem_conjSub_iff.mp hxH, by simpa using (inferInstance : N.Normal).conj_mem x hxN g⁻¹⟩
  rw [hH, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

omit [Finite Y] in
theorem card_map_of_inf_eq_bot {H : Subgroup Y} (hH : H ⊓ N = ⊥) :
    Nat.card (H.map (QuotientGroup.mk' N)) = Nat.card H :=
  (Nat.card_congr (TwistQ.mapEquiv (N := N) hH).toEquiv).symm

omit [Finite Y] in
theorem card_of_mem_conjClass_map (hRN : R ⊓ N = ⊥) {M : Subgroup (Y ⧸ N)}
    (hM : M ∈ CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N)))) :
    Nat.card M = Nat.card (tightCore R) := by
  obtain ⟨g, rfl⟩ := hM
  have hK : tightCore R ⊓ N = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right N (tightCore_le R)).trans hRN.le)
  rw [card_conjSub, ← TwistQ.tightCore_map hRN, card_map_of_inf_eq_bot hK]

theorem mem_omegaNbr_of_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1) {K J : Subgroup Y}
    (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R))
    (h : J.map (QuotientGroup.mk' N) ∈ omegaNbr
      (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (K.map (QuotientGroup.mk' N))) :
    J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hK0 : tightCore R ⊓ N = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right N (tightCore_le R)).trans hRN.le)
  obtain ⟨-, hne, _, ⟨M, hM, P₀, rfl⟩, hPbJ, hPbN⟩ := h
  obtain ⟨k, rfl⟩ := hK
  obtain ⟨j, rfl⟩ := hJ
  have hJN := conjSub_inf_eq_bot hK0 j
  set P : Subgroup Y := conjSub j (tightCore R) ⊓
    (Subgroup.map M.subtype (P₀ : Subgroup ↥M)).comap (QuotientGroup.mk' N) with hP
  have hPJ : P ≤ conjSub j (tightCore R) := inf_le_left
  have hPN : P ⊓ N = ⊥ := le_bot_iff.mp ((inf_le_inf_right N hPJ).trans hJN.le)
  have hPmap : P.map (QuotientGroup.mk' N) = Subgroup.map M.subtype (P₀ : Subgroup ↥M) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.2
    · intro hx
      obtain ⟨y, hyJ, hyx⟩ := hPbJ hx
      refine ⟨y, ⟨hyJ, ?_⟩, hyx⟩
      show QuotientGroup.mk' N y ∈ Subgroup.map M.subtype (P₀ : Subgroup ↥M)
      rw [hyx]
      exact hx
  have hcardP : Nat.card P = 2 ^ (Nat.card (conjSub j (tightCore R))).factorization 2 := by
    rw [← card_map_of_inf_eq_bot hPN, hPmap, Subgroup.card_map_of_injective M.subtype_injective,
      Sylow.card_eq_multiplicity, card_of_mem_conjClass_map hRN hM, card_conjSub]
  have hcardQ : Nat.card (P.subgroupOf (conjSub j (tightCore R))) =
      2 ^ (Nat.card (conjSub j (tightCore R))).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv, hcardP]
  refine ⟨⟨j, rfl⟩, fun h' => hne (by rw [h']), P,
    ⟨conjSub j (tightCore R), ⟨j, rfl⟩, Sylow.ofCard _ hcardQ, ?_⟩, hPJ, ?_⟩
  · rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPJ]
  · intro x hxP
    have hxb := hPbN hxP.2
    have h1 := conjSub_eq_of_mem_normalizer hxb
    rw [← TwistQ.conjSub_map, ← conjSub_mul] at h1
    have h2 : conjSub (x * k) (tightCore R) = conjSub k (tightCore R) := by
      by_contra hne'
      exact TwistQ.map_conjSub_ne hd hNc hN2 htN hnt hne' h1
    apply mem_normalizer_of_conjSub_eq
    rw [← conjSub_mul, h2]

theorem edgeless_map (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y)
    (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N)
    (hnt : ∀ y : Y, ∀ n ∈ N, y * t * y⁻¹ = t * n → n = 1) (h : TightEdgeless R) :
    TightEdgeless (R.map (QuotientGroup.mk' N)) := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hlift : ∀ M ∈ CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))),
      ∃ g : Y, M = (conjSub g (tightCore R)).map (QuotientGroup.mk' N) := by
    rintro _ ⟨gb, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
    exact ⟨g, by rw [TwistQ.conjSub_map, TwistQ.tightCore_map hRN]⟩
  intro Kb hKb Jb hJb hadj
  obtain ⟨k, rfl⟩ := hlift Kb hKb
  obtain ⟨j, rfl⟩ := hlift Jb hJb
  have hK : conjSub k (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨k, rfl⟩
  have hJ : conjSub j (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨j, rfl⟩
  rcases hadj with hadj | hadj
  · exact h _ hK _ hJ (Or.inl (mem_omegaNbr_of_map hd hNc hN2 htN hnt hK hJ hadj))
  · exact h _ hK _ hJ (Or.inr (mem_omegaNbr_of_map hd hNc hN2 htN hnt hJ hK hadj))

end Lift

end Thm6

end CFSG.ClassicalInvolution.Q3.TL4
