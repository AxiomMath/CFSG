module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevProof

open CFSG.Open CFSG.SectionRank

variable {p : ℕ}

theorem card_le_pow_pRank_of_injective {A G : Type*} [Group A] [Group G] [Finite G] [Fact p.Prime]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (f : A →* G)
    (hf : Function.Injective f) : Nat.card A ≤ p ^ pRank p (⊤ : Subgroup G) := by
  haveI : Finite A := Finite.of_injective f hf
  have hp : IsPGroup p A := fun a => ⟨1, by simpa using hpow a⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hp
  have hle : j ≤ pRank p (⊤ : Subgroup G) :=
    le_pRank_of_injective (Fact.out : p.Prime).one_lt hcomm hpow hj f hf le_top
  rw [hj]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hle

theorem pRank_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    [Fact p.Prime] :
    pRank p (⊤ : Subgroup (∀ i, G i)) = ∑ i, pRank p (⊤ : Subgroup (G i)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  apply le_antisymm
  · refine pRank_le hp1 (fun E _ hE => ?_)
    let π : ∀ i, (∀ j, G j) →* G i := fun i => Pi.evalMonoidHom G i
    have hEi : ∀ i, IsElemAbelian p (E.map (π i)) := fun i => isElemAbelian_map hE (π i)
    have hcard : ∀ i, Nat.card (E.map (π i)) ≤ p ^ pRank p (⊤ : Subgroup (G i)) := fun i =>
      card_le_pow_pRank_of_injective (hEi i).1.is_comm.comm
        (fun a => Subtype.ext (by simpa using (hEi i).2 a a.2)) (E.map (π i)).subtype
        Subtype.val_injective
    let ψ : E → ∀ i, E.map (π i) := fun x i => ⟨x.1 i, Subgroup.mem_map_of_mem (π i) x.2⟩
    have hψ : Function.Injective ψ := fun x y h =>
      Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
    calc Nat.card E ≤ Nat.card (∀ i, E.map (π i)) := Nat.card_le_card_of_injective ψ hψ
      _ = ∏ i, Nat.card (E.map (π i)) := Nat.card_pi
      _ ≤ ∏ i, p ^ pRank p (⊤ : Subgroup (G i)) := Finset.prod_le_prod' (fun i _ => hcard i)
      _ = p ^ ∑ i, pRank p (⊤ : Subgroup (G i)) := Finset.prod_pow_eq_pow_sum _ _ _
  · choose E hE using fun i => exists_pRank hp1 (⊤ : Subgroup (G i))
    let f : (∀ i, E i) →* ∀ i, G i :=
      Pi.monoidHom (fun i => (E i).subtype.comp (Pi.evalMonoidHom (fun i => ↥(E i)) i))
    have hf : Function.Injective f := fun a b h =>
      funext fun i => Subtype.ext (congrFun h i)
    have hcard : Nat.card (∀ i, E i) = p ^ ∑ i, pRank p (⊤ : Subgroup (G i)) := by
      rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun i _ => (hE i).2.2
    exact le_pRank_of_injective hp1
      (fun a b => funext fun i => (hE i).2.1.1.is_comm.comm (a i) (b i))
      (fun a => funext fun i => Subtype.ext (by simpa using (hE i).2.1.2 _ (a i).2))
      hcard f hf le_top

theorem pRank_multiplicative_zmod [Fact p.Prime] {a : ℕ} (ha : 1 ≤ a) :
    pRank p (⊤ : Subgroup (Multiplicative (ZMod (p ^ a)))) = 1 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a (Fact.out : p.Prime).ne_zero⟩
  have hcard : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  apply le_antisymm
  · refine pRank_le hp1 (fun E _ hE => ?_)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
    rw [pow_one, ← hord]
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one hgp)
  · have hdvd : p ∣ Nat.card (Multiplicative (ZMod (p ^ a))) := by
      rw [hcard]
      exact dvd_pow_self p (by omega)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hgp : g ^ p = 1 := by
      have h := pow_orderOf_eq_one g
      rwa [hg] at h
    refine le_pRank hp1 (E := Subgroup.zpowers g) le_top ⟨inferInstance, ?_⟩ ?_
    · rintro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgp, one_zpow]
    · rw [Nat.card_zpowers, hg, pow_one]

end RankChevProof

end CFSG.LocalAnalysis.RankThreeUC.S15
