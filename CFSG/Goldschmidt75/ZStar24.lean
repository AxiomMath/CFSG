module

public import CFSG.Goldschmidt75.Conj
public import CFSG.Goldschmidt.Steps.ZStarLemma
public import CFSG.Goldschmidt.OddCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

theorem oddCore_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : goldschmidtOddCore B = ⊥) : goldschmidtOddCore A = ⊥ := by
  rw [goldschmidtOddCore_eq_pPrimeCore] at h ⊢
  have h1 := CFSG.pPrimeCore_map_iso 2 e
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCore_subgroupOf_eq_bot {N H : Subgroup G} (hNH : N ≤ H)
    (hO : goldschmidtOddCore N = ⊥) : goldschmidtOddCore (N.subgroupOf H) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (subgroupOfEquivOfLe hNH) hO

omit [Finite G] in
theorem commutator_eq_bot_of_subgroupOf {A B H : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (h : ⁅A.subgroupOf H, B.subgroupOf H⁆ = ⊥) : ⁅A, B⁆ = ⊥ := by
  have := congrArg (Subgroup.map H.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA, inf_eq_left.mpr hB,
    Subgroup.map_bot] at this

@[expose] def Z24For (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (S N : Subgroup G), N.Normal → goldschmidtOddCore N = ⊥ → S ≤ T →
    fusionStronglyClosed (S : Set G) T → S ⊓ N = ⊥ → ⁅S, N⁆ = ⊥

theorem z24For_of_lt (IH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
    Z24For H) : Z24For G := by
  intro T S N hN hO hST hS hSN
  by_cases hcyc : IsCyclic S
  · have hab : IsMulCommutative S := by
      let := IsCyclic.commGroup (α := S)
      exact ⟨⟨fun a b => mul_comm a b⟩⟩
    exact CFSG.Goldschmidt.N6 G T S N hST hab hS
      (fun s _ => by rw [normalizer_eq_top_iff.mpr hN]; exact mem_top s) hO hSN
  rw [commutator_eq_bot_iff_le_centralizer]
  intro s hs
  set R := zpowers s
  have hRS : R ≤ S := zpowers_le.mpr hs
  have hRne : R ≠ S := by
    intro h
    apply hcyc
    have : IsCyclic R := inferInstance
    rwa [h] at this
  have hRN : R ⊓ N = ⊥ := le_bot_iff.mp ((inf_le_inf_right N hRS).trans hSN.le)
  set H₀ := N ⊔ R
  have hcapS : ∀ w ∈ S, w ∈ H₀ → w ∈ R := by
    intro w hw hwH
    obtain ⟨n, hn, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hwH
    have hnS : n ∈ S := by
      have := S.mul_mem hw (S.inv_mem (hRS hr)); simpa using this
    have hn1 : n = 1 := by
      have : n ∈ S ⊓ N := ⟨hnS, hn⟩
      rwa [hSN, mem_bot] at this
    rw [hn1, one_mul]; exact hr
  have hH₀ : H₀ ≠ ⊤ := by
    intro htop
    apply hRne
    exact le_antisymm hRS fun w hw => hcapS w hw (htop ▸ mem_top w)
  have hcard : Nat.card H₀ < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH₀)
  have hRp : IsPGroup 2 R := T.isPGroup'.to_le (hRS.trans hST)
  obtain ⟨T₀, hT₀⟩ := (hRp.comap_subtype (K := H₀)).exists_le_sylow
  obtain ⟨T'', hT''⟩ := (T₀.2.map H₀.subtype).exists_le_sylow
  obtain ⟨x, -, -, hxmem⟩ := exists_conj_le_sylow T T'' hST hS
  have hcap : ∀ w ∈ conjSub x S, w ∈ H₀ → w ∈ R := by
    intro w hw hwH
    obtain ⟨n, hn, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hwH
    have hrx : r ∈ conjSub x S :=
      hxmem r (hT'' ⟨⟨r, (le_sup_right : R ≤ H₀) hr⟩, hT₀ hr, rfl⟩) 1 (by simpa using hRS hr)
    have hnx : n ∈ conjSub x S := by
      have := (conjSub x S).mul_mem hw ((conjSub x S).inv_mem hrx); simpa using this
    have hn1 : n = 1 := by
      rw [mem_conjSub] at hnx
      have h1 : x * n * x⁻¹ ∈ S ⊓ N := ⟨hnx, hN.conj_mem n hn x⟩
      rw [hSN, mem_bot] at h1
      have := congrArg (fun z => x⁻¹ * z * x) h1
      simpa [mul_assoc] using this
    rw [hn1, one_mul]; exact hr
  have hRcl : fusionStronglyClosed (((R.subgroupOf H₀ : Subgroup H₀)) : Set H₀) T₀ := by
    intro a ha y hy
    have h1 : ((y⁻¹ * a * y : H₀) : G) ∈ (T'' : Subgroup G) := hT'' ⟨_, hy, rfl⟩
    have h2 : ((y⁻¹ * a * y : H₀) : G) ∈ conjSub x S :=
      hxmem _ h1 (y : G)⁻¹ (by simpa [mul_assoc] using hRS ha)
    exact hcap _ h2 (y⁻¹ * a * y).2
  have hN' : (N.subgroupOf H₀).Normal := Subgroup.normal_subgroupOf
  have hdisj : R.subgroupOf H₀ ⊓ N.subgroupOf H₀ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : (y : G) ∈ R ⊓ N := ⟨hy.1, hy.2⟩
    rw [hRN, mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have h := IH H₀ hcard T₀ (R.subgroupOf H₀) (N.subgroupOf H₀) hN'
    (oddCore_subgroupOf_eq_bot le_sup_left hO) hT₀ hRcl hdisj
  exact commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_subgroupOf le_sup_right le_sup_left h) (mem_zpowers s)

theorem z24For (G : Type) [Group G] [Finite G] : Z24For G := by
  suffices key : ∀ n, ∀ (H : Type) [Group H] [Finite H], Nat.card H = n → Z24For H from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hn
  exact z24For_of_lt fun K _ _ hK => ih _ (hn ▸ hK) K rfl

theorem commutator_eq_bot_of_inf_eq_bot (T : Sylow 2 G) {S N : Subgroup G} [N.Normal]
    (hO : goldschmidtOddCore N = ⊥) (hST : S ≤ T) (hS : fusionStronglyClosed (S : Set G) T)
    (hSN : S ⊓ N = ⊥) : ⁅S, N⁆ = ⊥ :=
  z24For G T S N inferInstance hO hST hS hSN

end CFSG.Goldschmidt75
