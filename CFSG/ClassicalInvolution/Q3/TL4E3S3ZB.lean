module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ZA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3Z

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem mem_normalizer_of_conjSub_eq {p : Y} {K : Subgroup Y} (h : conjSub p K = K) :
    p ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact conj_mem_conjSub hx
  · intro hx
    rw [← h, mem_conjSub_iff] at hx
    have e : p⁻¹ * (p * x * p⁻¹) * p = x := by group
    rwa [e] at hx

omit [Finite Y] in
theorem card_conjSub_eq (g : Y) (H : Subgroup Y) : Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

omit [Finite Y] in
theorem card_map_mk_eq {N : Subgroup Y} [N.Normal] {H : Subgroup Y} (h : H ⊓ N = ⊥) :
    Nat.card ↥(H.map (QuotientGroup.mk' N)) = Nat.card ↥H :=
  (Nat.card_congr (TwistQ.mapEquiv h).toEquiv).symm

omit [Finite Y] in
theorem conjSub_inf_eq_bot {N : Subgroup Y} [N.Normal] {H : Subgroup Y} (h : H ⊓ N = ⊥)
    (g : Y) : conjSub g H ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxN' : g⁻¹ * x * g ∈ N := by
    have := (inferInstance : N.Normal).conj_mem _ hxN g⁻¹
    rwa [inv_inv] at this
  have h1 : g⁻¹ * x * g ∈ H ⊓ N := Subgroup.mem_inf.mpr ⟨mem_conjSub_iff.mp hxH, hxN'⟩
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem exists_sylow_of_card {J P : Subgroup Y} (hPJ : P ≤ J) {M : Type} [Group M] [Finite M]
    (P₀ : Sylow 2 M) (hP : Nat.card ↥P = Nat.card ↥(P₀ : Subgroup M))
    (hJM : Nat.card ↥J = Nat.card M) :
    ∃ Q : Sylow 2 ↥J, P = (Q : Subgroup ↥J).map J.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card ↥(P.subgroupOf J) = 2 ^ (Nat.card ↥J).factorization 2 := by
    rw [hJM]
    exact ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv).trans hP).trans
      (Sylow.card_eq_multiplicity P₀)
  exact ⟨Sylow.ofCard _ hc, by rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPJ]⟩

omit [Finite Y] in
theorem conjSub_le_normalizer {N : Subgroup Y} [N.Normal] (hNc : N ≤ Subgroup.center Y)
    {K : Subgroup Y} {p : Y}
    (hp : QuotientGroup.mk' N p ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N))) :
    conjSub p K ≤ Subgroup.normalizer (K : Set Y) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := hx
  have h1 : QuotientGroup.mk' N (p * k * p⁻¹) ∈ K.map (QuotientGroup.mk' N) := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hp _).mp ⟨k, hk, rfl⟩
  obtain ⟨k', hk', hkk'⟩ := h1
  have hn : k'⁻¹ * (p * k * p⁻¹) ∈ N := by
    rw [← QuotientGroup.eq]
    exact hkk'
  show p * k * p⁻¹ ∈ Subgroup.normalizer (K : Set Y)
  rw [show p * k * p⁻¹ = k' * (k'⁻¹ * (p * k * p⁻¹)) by group]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk') (Subgroup.center_le_normalizer _ (hNc hn))

theorem not_edgeless_of_mem_omegaNbr_map {N : Subgroup Y} [N.Normal] (hd : TightDatum R S t)
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (a b : Y)
    (hJ : (conjSub b (tightCore R)).map (QuotientGroup.mk' N) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
        ((conjSub a (tightCore R)).map (QuotientGroup.mk' N))) : ¬ TightEdgeless R := by
  intro hE
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hK0N : tightCore R ⊓ N = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right N (tightCore_le R)).trans hRN.le)
  obtain ⟨-, hne, Pb, hPb, hPbJ, hPbN⟩ := hJ
  have hKΩ : conjSub a (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨a, rfl⟩
  have hJΩ : conjSub b (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨b, rfl⟩
  have hJK : conjSub b (tightCore R) ≠ conjSub a (tightCore R) := fun h => hne (by rw [h])
  let P : Subgroup Y := conjSub b (tightCore R) ⊓ Pb.comap (QuotientGroup.mk' N)
  have hPJ : P ≤ conjSub b (tightCore R) := inf_le_left
  have hPmap : P.map (QuotientGroup.mk' N) = Pb := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact (Subgroup.mem_inf.mp hp).2
    · intro pb hpb
      obtain ⟨j, hj, rfl⟩ := hPbJ hpb
      exact ⟨j, Subgroup.mem_inf.mpr ⟨hj, hpb⟩, rfl⟩
  have hKpN : ∀ p ∈ P, conjSub p (conjSub a (tightCore R)) ≤
      Subgroup.normalizer ((conjSub a (tightCore R) : Subgroup Y) : Set Y) := fun p hp =>
    conjSub_le_normalizer hNc (hPbN (Subgroup.mem_inf.mp hp).2)
  by_cases hall : ∀ p ∈ P, conjSub p (conjSub a (tightCore R)) = conjSub a (tightCore R)
  ·
    have hPN : P ≤ Subgroup.normalizer ((conjSub a (tightCore R) : Subgroup Y) : Set Y) :=
      fun p hp => mem_normalizer_of_conjSub_eq (hall p hp)
    obtain ⟨Mb, hMb, Pb₀, rfl⟩ := hPb
    obtain ⟨gb, rfl⟩ := hMb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N gb
    have hMeq : conjSub (QuotientGroup.mk' N c) (tightCore (R.map (QuotientGroup.mk' N))) =
        (conjSub c (tightCore R)).map (QuotientGroup.mk' N) := by
      rw [TwistQ.conjSub_map, TwistQ.tightCore_map hRN]
    have hPinf : P ⊓ N = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right N hPJ).trans (conjSub_inf_eq_bot hK0N b).le)
    have hP : Nat.card ↥P = Nat.card ↥Pb₀.toSubgroup := by
      rw [← card_map_mk_eq hPinf, hPmap]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    have hJM : Nat.card ↥(conjSub b (tightCore R)) = Nat.card ↥(conjSub (QuotientGroup.mk' N c)
        (tightCore (R.map (QuotientGroup.mk' N)))) := by
      rw [hMeq, card_map_mk_eq (conjSub_inf_eq_bot hK0N c), card_conjSub_eq, card_conjSub_eq]
    obtain ⟨Q, hQ⟩ := exists_sylow_of_card hPJ Pb₀ hP hJM
    have hPR : P ∈ RSet (CoreAssembly.conjClass (tightCore R)) := ⟨_, hJΩ, Q, hQ⟩
    have hadj : Disconnected.dAdj (CoreAssembly.conjClass (tightCore R))
        (conjSub a (tightCore R)) (conjSub b (tightCore R)) :=
      Or.inl ⟨hJΩ, hJK, P, hPR, hPJ, hPN⟩
    exact hE _ hKΩ _ hJΩ hadj
  ·
    push Not at hall
    obtain ⟨p, hp, hpK⟩ := hall
    have hKpΩ : conjSub p (conjSub a (tightCore R)) ∈ CoreAssembly.conjClass (tightCore R) :=
      ⟨p * a, conjSub_mul p a (tightCore R)⟩
    obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥(conjSub p (conjSub a (tightCore R)))) := inferInstance
    have hQR : (Q : Subgroup _).map (conjSub p (conjSub a (tightCore R))).subtype ∈
        RSet (CoreAssembly.conjClass (tightCore R)) := ⟨_, hKpΩ, Q, rfl⟩
    have hadj : Disconnected.dAdj (CoreAssembly.conjClass (tightCore R))
        (conjSub a (tightCore R)) (conjSub p (conjSub a (tightCore R))) :=
      Or.inl ⟨hKpΩ, hpK, _, hQR, Subgroup.map_subtype_le _,
        (Subgroup.map_subtype_le _).trans (hKpN p hp)⟩
    exact hE _ hKΩ _ hKpΩ hadj

theorem edgeless_map {N : Subgroup Y} [N.Normal] (hd : TightDatum R S t)
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) (hE : TightEdgeless R) :
    TightEdgeless (R.map (QuotientGroup.mk' N)) := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  have hlift : ∀ M ∈ CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))),
      ∃ g : Y, M = (conjSub g (tightCore R)).map (QuotientGroup.mk' N) := by
    rintro _ ⟨gb, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
    exact ⟨g, by rw [TwistQ.conjSub_map, TwistQ.tightCore_map hRN]⟩
  intro Kb hKb Jb hJb hadj
  obtain ⟨a, rfl⟩ := hlift Kb hKb
  obtain ⟨b, rfl⟩ := hlift Jb hJb
  rcases hadj with h | h
  · exact not_edgeless_of_mem_omegaNbr_map hd hNc hN2 htN a b h hE
  · exact not_edgeless_of_mem_omegaNbr_map hd hNc hN2 htN b a h hE

theorem edgelessMember3_quot (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) (hE : TightEdgeless R) :
    EdgelessMember3 (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (TwistQ.sylowMap (Subgroup.center Y) S) (QuotientGroup.mk' (Subgroup.center Y) t) := by
  have hN2 := isPGroup_center hc
  have htN := not_mem_center hc hE2
  exact ⟨TwistQ.datum hd hN2 htN (noTwin hd hE),
    tightClsR_three_iff.mpr (TwistQ.cls hd le_rfl hN2 htN hc), edgeless_map hd le_rfl hN2 htN hE⟩

end CFSG.ClassicalInvolution.Q3.TL4.E3S3Z
