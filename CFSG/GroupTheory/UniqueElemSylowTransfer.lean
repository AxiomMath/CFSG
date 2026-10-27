module

public import CFSG.GroupTheory.UniqueElemSylow
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GroupTheory

variable {p k : ℕ} {G : Type*} [Group G]

private theorem card_map_of_inf_ker_eq_bot {H : Type*} [Group H] {f : G →* H} {P A : Subgroup G}
    (hPN : P ⊓ f.ker = ⊥) (hA : A ≤ P) : Nat.card (A.map f) = Nat.card A := by
  have hker : (f.subgroupMap A).ker = ⊥ := by
    rw [Subgroup.ker_subgroupMap, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    exact bot_unique (hPN ▸ inf_le_inf hA le_rfl)
  have hinj : Function.Injective (f.subgroupMap A) := (MonoidHom.ker_eq_bot_iff _).mp hker
  exact (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap A)
    ⟨hinj, f.subgroupMap_surjective A⟩).toEquiv).symm

private theorem isElemAbelian_comap_inf {H : Type*} [Group H] {f : G →* H} {P : Subgroup G}
    {B : Subgroup H} (hPN : P ⊓ f.ker = ⊥) (hB : CFSG.Open.IsElemAbelian p B) :
    CFSG.Open.IsElemAbelian p (B.comap f ⊓ P) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hxP : (x : G) ∈ P := x.2.2
    have hyP : (y : G) ∈ P := y.2.2
    have hcomm : f (x : G) * f (y : G) = f (y : G) * f (x : G) :=
      congrArg Subtype.val
        (hB.1.is_comm.comm ⟨f (x : G), Subgroup.mem_comap.mp x.2.1⟩
          ⟨f (y : G), Subgroup.mem_comap.mp y.2.1⟩)
    have hmem : (x : G) * (y : G) * ((y : G) * (x : G))⁻¹ ∈ P ⊓ f.ker := by
      refine ⟨P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem (P.mul_mem hyP hxP)), ?_⟩
      show f ((x : G) * (y : G) * ((y : G) * (x : G))⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hcomm, mul_inv_cancel]
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hPN ▸ hmem))
  · have hxP : (x : G) ∈ P := hx.2
    have hxker : f (x : G) ∈ B := hx.1
    have hmem : (x : G) ^ p ∈ P ⊓ f.ker := by
      refine ⟨P.pow_mem hxP p, ?_⟩
      show f ((x : G) ^ p) = 1
      rw [map_pow]
      exact hB.2 _ hxker
    exact Subgroup.mem_bot.mp (hPN ▸ hmem)

private theorem map_comap_inf_eq {H : Type*} [Group H] {f : G →* H} {P : Subgroup G}
    {B : Subgroup H} (hB : B ≤ P.map f) : (B.comap f ⊓ P).map f = B := by
  refine le_antisymm ?_ ?_
  · calc (B.comap f ⊓ P).map f ≤ (B.comap f).map f := Subgroup.map_mono inf_le_left
      _ = f.range ⊓ B := Subgroup.map_comap_eq f B
      _ ≤ B := inf_le_right
  · intro y hy
    obtain ⟨p, hpP, hpy⟩ := hB hy
    rw [← hpy]
    refine Subgroup.mem_map_of_mem f ⟨?_, hpP⟩
    show f p ∈ B
    rw [hpy]
    exact hy

private theorem comap_map_inf_eq {H : Type*} [Group H] {f : G →* H} {P A : Subgroup G}
    (hPN : P ⊓ f.ker = ⊥) (hA : A ≤ P) : (A.map f).comap f ⊓ P = A := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, haA, hax⟩ := hx.1
    have hmem : a⁻¹ * x ∈ P ⊓ f.ker := by
      refine ⟨P.mul_mem (P.inv_mem (hA haA)) hx.2, ?_⟩
      show f (a⁻¹ * x) = 1
      rw [map_mul, map_inv, hax, inv_mul_cancel]
    have h1 : a⁻¹ * x = 1 := Subgroup.mem_bot.mp (hPN ▸ hmem)
    exact (inv_mul_eq_one.mp h1) ▸ haA
  · intro x hx
    exact ⟨Subgroup.mem_map_of_mem f hx, hA hx⟩

private theorem existsUnique_map_iff {H : Type*} [Group H] {f : G →* H} {P : Subgroup G}
    (hPN : P ⊓ f.ker = ⊥) :
    (∃! A : Subgroup G, A ≤ P ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ k) ↔
      (∃! A' : Subgroup H, A' ≤ P.map f ∧ CFSG.Open.IsElemAbelian p A' ∧
        Nat.card A' = p ^ k) := by
  constructor
  · rintro ⟨A, ⟨hAP, hAel, hAcard⟩, huniq⟩
    refine ⟨A.map f, ⟨Subgroup.map_mono hAP, hAel.map f, ?_⟩, ?_⟩
    · rw [card_map_of_inf_ker_eq_bot hPN hAP, hAcard]
    · intro B' hB'
      have hBP : B'.comap f ⊓ P ≤ P := inf_le_right
      have hBel : CFSG.Open.IsElemAbelian p (B'.comap f ⊓ P) :=
        isElemAbelian_comap_inf hPN hB'.2.1
      have hBcard : Nat.card ↥(B'.comap f ⊓ P) = p ^ k := by
        rw [← card_map_of_inf_ker_eq_bot hPN hBP, map_comap_inf_eq hB'.1, hB'.2.2]
      have hBA : B'.comap f ⊓ P = A := huniq _ ⟨hBP, hBel, hBcard⟩
      rw [← map_comap_inf_eq hB'.1, hBA]
  · rintro ⟨A', ⟨hA'P, hA'el, hA'card⟩, huniq⟩
    refine ⟨A'.comap f ⊓ P, ⟨inf_le_right, isElemAbelian_comap_inf hPN hA'el, ?_⟩, ?_⟩
    · rw [← card_map_of_inf_ker_eq_bot hPN inf_le_right, map_comap_inf_eq hA'P, hA'card]
    · intro A hA
      have hmapA : A.map f = A' := by
        refine huniq _ ⟨Subgroup.map_mono hA.1, hA.2.1.map f, ?_⟩
        rw [card_map_of_inf_ker_eq_bot hPN hA.1, hA.2.2]
      rw [← comap_map_inf_eq hPN hA.1, hmapA]

private theorem le_of_isPGroup_of_pow_mem [Fact p.Prime] {S : Subgroup G} {m : ℕ}
    (hm : ¬ p ∣ m) (hpow : ∀ g : G, g ^ m ∈ S) {H : Subgroup G} (hH : IsPGroup p H) :
    H ≤ S := by
  intro x hx
  obtain ⟨y, hy⟩ := (hH.powEquiv' hm).surjective ⟨x, hx⟩
  have hy' : ((y : H) : G) ^ m = x := congrArg Subtype.val hy
  rw [← hy']
  exact hpow _

theorem UniqueElemSylow.quotient_iff [Finite G] [Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) :
    UniqueElemSylow p k (G ⧸ N) ↔ UniqueElemSylow p k G := by
  let f : G →* G ⧸ N := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hker : f.ker = N := QuotientGroup.ker_mk' N
  have hPSylow : ∀ P : Sylow p G, (P : Subgroup G) ⊓ f.ker = ⊥ := by
    intro P
    rw [hker]
    exact disjoint_iff.mp (IsPGroup.disjoint_of_coprime P.2 IsPGroup.card
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hN))
  constructor
  · intro h P
    exact (existsUnique_map_iff (f := f) (P := (P : Subgroup G)) (hPSylow P)).mpr
      (h (Sylow.mapSurjective hf P))
  · intro h P'
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (p := p) hf P'
    rw [← hP]
    exact (existsUnique_map_iff (f := f) (P := (P : Subgroup G)) (hPSylow P)).mp (h P)

theorem UniqueElemSylow.subgroup_of_pow_mem [Finite G] [Fact p.Prime] (S : Subgroup G) {m : ℕ}
    (hm : ¬ p ∣ m) (hpow : ∀ g : G, g ^ m ∈ S) (h : UniqueElemSylow p k G) :
    UniqueElemSylow p k S := by
  intro P
  obtain ⟨Q, hle⟩ := IsPGroup.exists_le_sylow (P.2.map S.subtype)
  have hQS : (Q : Subgroup G) ≤ S := le_of_isPGroup_of_pow_mem hm hpow Q.2
  have hPS : (P : Subgroup S) ≤ (Q : Subgroup G).subgroupOf S :=
    Subgroup.map_le_iff_le_comap.mp hle
  have hPQ : (P : Subgroup S) = (Q : Subgroup G).subgroupOf S :=
    (P.is_maximal' (Q.subtype hQS).2 hPS).symm
  obtain ⟨A, hA, huniq⟩ := h Q
  have hAS : A ≤ S := hA.1.trans hQS
  refine ⟨A.subgroupOf S, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hPQ]
    exact Subgroup.subgroupOf_mono S hA.1
  · exact hA.2.1.subgroupOf S
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv, hA.2.2]
  · intro B hB
    have hBQ : B.map S.subtype ≤ (Q : Subgroup G) := by
      calc B.map S.subtype ≤ (P : Subgroup S).map S.subtype := Subgroup.map_mono hB.1
        _ = ((Q : Subgroup G).subgroupOf S).map S.subtype := by rw [hPQ]
        _ = (Q : Subgroup G) ⊓ S := Subgroup.subgroupOf_map_subtype _ _
        _ = (Q : Subgroup G) := inf_eq_left.mpr hQS
    have hBqel : CFSG.Open.IsElemAbelian p (B.map S.subtype) := hB.2.1.map S.subtype
    have hBqcard : Nat.card (B.map S.subtype) = p ^ k := by
      rw [Subgroup.card_map_of_injective S.subtype_injective, hB.2.2]
    have hBmap : B.map S.subtype = A := huniq _ ⟨hBQ, hBqel, hBqcard⟩
    rw [← hBmap]
    exact (Subgroup.comap_map_eq_self_of_injective S.subtype_injective B).symm

end CFSG.GroupTheory
