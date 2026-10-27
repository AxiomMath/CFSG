module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrFact
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

namespace SAFyGH

abbrev A5 : Type := alternatingGroup (Fin 5)

@[expose] def zW8 : W8 := ⟨fun _ => DihedralGroup.r 2, 1⟩

@[expose] def sW8 : W8 := ⟨fun _ => 1, Multiplicative.ofAdd (1 : ZMod 2)⟩

@[expose] def tW8 : W8 := ⟨fun x => if x = 1 then DihedralGroup.r 1 else 1, 1⟩

@[expose] def uW8 : W8 := ⟨fun x => if x = 1 then DihedralGroup.sr 0 else 1, 1⟩

set_option maxRecDepth 100000 in
theorem center_W8 (w : W8) (hw : w ∈ center W8) : w = 1 ∨ w = zW8 := by
  have h1 := mem_center_iff.1 hw sW8
  have h2 := mem_center_iff.1 hw tW8
  have h3 := mem_center_iff.1 hw uW8
  revert w
  decide

theorem center_unique {P : Type*} [Group P] (ι : P ≃* W8) {a b : P} (ha : a ∈ center P)
    (hb : b ∈ center P) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have hc : ∀ {c : P}, c ∈ center P → c ≠ 1 → ι c = zW8 := by
    intro c hc hc1
    have hcW : ι c ∈ center W8 := by
      rw [mem_center_iff]
      intro w
      obtain ⟨p, rfl⟩ := ι.surjective w
      rw [← map_mul, ← map_mul, mem_center_iff.1 hc p]
    rcases center_W8 _ hcW with h | h
    · exact absurd (ι.injective (h.trans (map_one ι).symm)) hc1
    · exact h
  exact ι.injective ((hc ha ha1).trans (hc hb hb1).symm)

set_option maxRecDepth 100000 in
theorem center_A5 : ∀ a : A5, (∀ c : A5, c * a = a * c) → a = 1 := by decide

theorem card_A5 : Nat.card A5 = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem center_A5A5 (p : A5 × A5) (hp : ∀ q : A5 × A5, q * p = p * q) : p = 1 := by
  have h1 : p.1 = 1 := center_A5 _ fun c => congrArg Prod.fst (hp (c, 1))
  have h2 : p.2 = 1 := center_A5 _ fun c => congrArg Prod.snd (hp (1, c))
  exact Prod.ext h1 h2

theorem card_A5A5 : Nat.card (A5 × A5) = 3600 := by
  rw [Nat.card_prod, card_A5]

variable {X : Type} [Group X] [Finite X]

theorem exists_ne_one_mem_inf_sylow {N : Subgroup X} [N.Normal] (hN : 2 ∣ Nat.card N)
    (P : Sylow 2 X) : ∃ n ∈ N ⊓ (P : Subgroup X), n ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' 2 hN
  have hp : IsPGroup 2 (zpowers ((n : N) : X)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hn, pow_one]
  obtain ⟨P', hP'⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P'
  have hnP' : ((n : N) : X) ∈ (P' : Subgroup X) := hP' (mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hnP'
  have key : g⁻¹ * ((n : N) : X) * g ∈ (P : Subgroup X) := by
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hnP'
  refine ⟨g⁻¹ * ((n : N) : X) * g, ⟨?_, key⟩, ?_⟩
  · have h := (inferInstance : N.Normal).conj_mem _ (n : N).2 g⁻¹
    simpa [mul_assoc] using h
  · intro h
    have h1 : ((n : N) : X) = 1 := by
      calc ((n : N) : X) = g * (g⁻¹ * ((n : N) : X) * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have : (n : N) = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hn
    omega

theorem centralizer_layer_eq_bot (hO : CFSG.pPrimeCore 2 X = ⊥) (E : Subgroup X) [E.Normal]
    (ψ : E ≃* A5 × A5) (P : Sylow 2 X) (ι : ↥(P : Subgroup X) ≃* W8) :
    centralizer (E : Set X) = ⊥ := by
  by_contra hne
  set N := centralizer (E : Set X) with hN
  have hNn : N.Normal := ⟨fun n hn g e he => by
    have hn' := mem_centralizer_iff.1 hn
    have he' : g⁻¹ * e * g⁻¹⁻¹ ∈ E := (inferInstance : E.Normal).conj_mem _ he g⁻¹
    have := hn' _ he'
    calc e * (g * n * g⁻¹) = g * ((g⁻¹ * e * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * e * g)) * g⁻¹ := by simpa using congrArg (fun y => g * y * g⁻¹) this
      _ = g * n * g⁻¹ * e := by group⟩
  have hEN : E ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxN⟩ := hx
    have hxc : ∀ q : A5 × A5, q * ψ ⟨x, hxE⟩ = ψ ⟨x, hxE⟩ * q := by
      intro q
      obtain ⟨y, rfl⟩ := ψ.surjective q
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_iff.1 hxN y y.2
    have h1 := center_A5A5 _ hxc
    have h2 : (⟨x, hxE⟩ : E) = 1 := ψ.injective (h1.trans (map_one ψ).symm)
    exact (Subtype.ext_iff.1 h2)
  have hE2 : 2 ∣ Nat.card E := by
    rw [Nat.card_congr ψ.toEquiv, card_A5A5]
    norm_num
  have hN2 : 2 ∣ Nat.card N := by
    by_contra h
    have hcop : Nat.Coprime 2 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h
    exact hne (CFSG.pPrimeCore_eq_bot_iff.1 hO N hNn hcop)
  obtain ⟨n₁, ⟨hn₁N, hn₁P⟩, hn₁⟩ := exists_ne_one_mem_inf_sylow hN2 P
  obtain ⟨e₁, ⟨he₁E, he₁P⟩, he₁⟩ := exists_ne_one_mem_inf_sylow hE2 P
  set Pg : Subgroup X := (P : Subgroup X) with hPg
  have : Group.IsNilpotent ↥Pg := IsPGroup.isNilpotent P.isPGroup'
  have hAE : E.subgroupOf Pg ≠ ⊥ := by
    intro h
    have : (⟨e₁, he₁P⟩ : ↥Pg) ∈ E.subgroupOf Pg := he₁E
    rw [h, mem_bot] at this
    exact he₁ (Subtype.ext_iff.1 this)
  have hAN : N.subgroupOf Pg ≠ ⊥ := by
    intro h
    have : (⟨n₁, hn₁P⟩ : ↥Pg) ∈ N.subgroupOf Pg := hn₁N
    rw [h, mem_bot] at this
    exact hn₁ (Subtype.ext_iff.1 this)
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hAE)
  obtain ⟨b, hb⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hAN)
  have hab : (a : ↥Pg) = b :=
    center_unique ι (a.2.2) (b.2.2) (fun h => ha (Subtype.ext h)) (fun h => hb (Subtype.ext h))
  have hx : ((a : ↥Pg) : X) ∈ E ⊓ N := ⟨a.2.1, hab ▸ b.2.1⟩
  rw [hEN, mem_bot] at hx
  exact ha (Subtype.ext (Subtype.ext hx))

end SAFyGH

end CFSG.EvenSporadicStandard.TwoHS
