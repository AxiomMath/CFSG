module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools
import CFSG.Permutation.TranspositionCentralizer
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.PermSylowTwo.Pairing

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm CFSG.ABGLocalTools

private instance fact_prime_two_g45j : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem exists_fixedPoint_g45j {α : Type*} [Fintype α] [DecidableEq α]
    (hodd : Odd (Nat.card α)) {P : Subgroup (Perm α)} (hP : IsPGroup 2 P) :
    ∃ f, ∀ p ∈ P, p f = f := by
  have h2 : ¬ 2 ∣ Nat.card α := by
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨f, hf⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α h2
  exact ⟨f, fun p hp => by simpa using hf ⟨p, hp⟩⟩

private theorem isCoatom_stabilizer_g45j {α : Type*} [Fintype α] [DecidableEq α]
    [Nontrivial α] (a : α) :
    IsCoatom (MulAction.stabilizer (Perm α) a) :=
  @MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (Perm α) _ α _
    ‹Nontrivial α› (Equiv.Perm.instIsPreprimitive) a

private theorem exists_two_ne_g45j {α : Type*} [Fintype α] [DecidableEq α] (f : α)
    (h5 : 5 ≤ Fintype.card α) : ∃ a b : α, a ≠ f ∧ b ≠ f ∧ b ≠ a := by
  classical
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({f} : Finset α)) (t := Finset.univ) (by
      rw [Finset.card_singleton, Finset.card_univ]
      omega)
  have haf : a ≠ f := by simpa using ha
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({f, a} : Finset α)) (t := Finset.univ) (by
      rw [Finset.card_pair (Ne.symm haf), Finset.card_univ]
      omega)
  have hb' : b ≠ f ∧ b ≠ a := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hb
  exact ⟨a, b, haf, hb'.1, hb'.2⟩

private theorem commute_of_mem_fixingSubgroup_g45j {α : Type*} [Fintype α] [DecidableEq α]
    {s : Set α} {x y : Perm α} (hx : x ∈ fixingSubgroup (Perm α) s)
    (hy : y ∈ fixingSubgroup (Perm α) sᶜ) : Commute x y := by
  refine Equiv.Perm.Disjoint.commute ?_
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro a
  by_cases ha : a ∈ s
  · left
    simpa using (mem_fixingSubgroup_iff (Perm α)).mp hx a ha
  · right
    simpa using (mem_fixingSubgroup_iff (Perm α)).mp hy a (by simpa using ha)

private theorem inf_fixingSubgroup_compl_g45j {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) :
    fixingSubgroup (Perm α) ((s : Set α)ᶜ) ⊓ fixingSubgroup (Perm α) (s : Set α) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun a => ?_
  by_cases ha : a ∈ s
  · simpa using (mem_fixingSubgroup_iff (Perm α)).mp hx.2 a ha
  · have ha' : a ∈ ((s : Set α)ᶜ) := by simpa using ha
    simpa using (mem_fixingSubgroup_iff (Perm α)).mp hx.1 a ha'

private theorem apply_mem_of_mem_fixingSubgroup_compl_g45j {α : Type*} [Fintype α]
    [DecidableEq α] {s : Finset α} {x : Perm α}
    (hx : x ∈ fixingSubgroup (Perm α) ((s : Set α)ᶜ)) {a : α} (ha : a ∈ s) : x a ∈ s := by
  by_contra h
  have h1 : x (x a) = x a :=
    (mem_fixingSubgroup_iff (Perm α)).mp hx (x a) (by simpa using h)
  have h2 : x a = a := x.injective h1
  rw [h2] at h
  exact h ha

private theorem not_three_dvd_orderOf_g45j {G : Type*} [Group G] {K : Subgroup G}
    (hK : IsPGroup 2 K) {x : G} (hx : x ∈ K) : ¬ 3 ∣ orderOf x := by
  intro h3
  have hcop : (orderOf (⟨x, hx⟩ : K)).Coprime 3 :=
    hK.orderOf_coprime (by norm_num) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hcop
  have h1 : 3 = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm h3
  norm_num at h1

private theorem card_fixingSubgroup_compl_g45j {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) :
    Nat.card (fixingSubgroup (Perm α) ((s : Set α)ᶜ)) = Nat.card (Perm s) := by
  classical
  rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_range_ofSubtype
    (s := (s : Set α))]
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) Perm.ofSubtype_injective]
  exact Nat.card_congr (Subgroup.topEquiv).toEquiv

private theorem card_fixingSubgroup_compl_of_card_g45j {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.card = 3) :
    Nat.card (fixingSubgroup (Perm α) ((s : Set α)ᶜ)) = 6 := by
  rw [card_fixingSubgroup_compl_g45j, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_coe, hs]
  decide

private theorem swap_mem_fixingSubgroup_compl_g45j {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    Equiv.swap a b ∈ fixingSubgroup (Perm α) ((s : Set α)ᶜ) := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb))

private theorem three_dvd_swap_mul_swap_g45j {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ∣ orderOf (Equiv.swap a b * Equiv.swap a c) :=
  three_dvd_orderOf_mul (x := Equiv.swap a b) (y := Equiv.swap a c) hab hac hbc
    (Equiv.swap_apply_left a b) (Equiv.swap_apply_right a b)
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc))
    (Equiv.swap_apply_left a c) (Equiv.swap_apply_right a c)
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc)

private theorem three_dvd_swap_mul_swap'_g45j {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    3 ∣ orderOf (Equiv.swap a b * Equiv.swap b c) := by
  have h := three_dvd_orderOf_mul (x := Equiv.swap b a) (y := Equiv.swap b c)
    (a := b) (b := a) (e := c) (Ne.symm hab) hbc hac
    (Equiv.swap_apply_left b a) (Equiv.swap_apply_right b a)
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hbc) (Ne.symm hac))
    (Equiv.swap_apply_left b c) (Equiv.swap_apply_right b c)
    (Equiv.swap_apply_of_ne_of_ne hab hac)
  rwa [Equiv.swap_comm b a] at h

private structure Base_g45j {n : ℕ} (P : Subgroup (Perm (Fin n))) where
  f : Fin n
  hfP : ∀ p ∈ P, p f = f
  X₁ : Subgroup (Perm (Fin n))
  hX₁ : X₁ = MulAction.stabilizer (Perm (Fin n)) f
  hPX₁ : P ≤ X₁
  hX₁coatom : IsCoatom X₁
  a : Fin n
  b : Fin n
  Δ₀ : Finset (Fin n)
  ha : a ≠ f
  hbf : b ≠ f
  hba : b ≠ a
  hΔ₀ : Δ₀ = {f, a, b}
  hΔ₀card : Δ₀.card = 3

private theorem exists_base_g45j {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    {P : Subgroup (Perm (Fin n))} (hP : IsSylowOf 2 P ⊤) :
    Nonempty (Base_g45j P) := by
  obtain ⟨f, hfP⟩ := exists_fixedPoint_g45j (by simpa using hn) hP.isPGroup
  let X₁ : Subgroup (Perm (Fin n)) := MulAction.stabilizer (Perm (Fin n)) f
  have hPX₁ : P ≤ X₁ := fun p hp => (MulAction.mem_stabilizer_iff).mpr (hfP p hp)
  have hnontriv : Nontrivial (Fin n) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩⟩
  have hX₁coatom : IsCoatom X₁ :=
    @isCoatom_stabilizer_g45j (Fin n) _ _ hnontriv f
  obtain ⟨a, b, haf, hbf, hba⟩ := exists_two_ne_g45j f (by simpa using h5)
  refine ⟨⟨f, hfP, X₁, rfl, hPX₁, hX₁coatom, a, b, {f, a, b}, haf, hbf, hba, rfl, ?_⟩⟩
  have h1 : f ∉ ({a, b} : Finset (Fin n)) := by simp [Ne.symm haf, Ne.symm hbf]
  have h2 : a ∉ ({b} : Finset (Fin n)) := by simp [hba.symm]
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_singleton]

private structure Data_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} (B : Base_g45j P) where
  A₀ : Subgroup (Perm (Fin n))
  A₁ : Subgroup (Perm (Fin n))
  B₀ : Subgroup (Perm (Fin n))
  hA₀ : A₀ = fixingSubgroup (Perm (Fin n)) ((B.Δ₀ : Set (Fin n))ᶜ)
  hA₁ : A₁ = fixingSubgroup (Perm (Fin n)) (B.Δ₀ : Set (Fin n))
  hB₀ : IsSylowOf 2 B₀ A₁
  σ₀ : Perm (Fin n)
  hσ₀ : σ₀ = Equiv.swap B.a B.b
  hσ₀A₀ : σ₀ ∈ A₀
  hσ₀swap : σ₀.IsSwap
  hσ₀order : orderOf σ₀ = 2
  hA₀A₁ : A₀ ⊓ A₁ = ⊥
  hB₀disj : A₀ ⊓ B₀ = ⊥
  hA₀cent : A₀ ≤ Subgroup.centralizer (B₀ : Set (Perm (Fin n)))
  hA₀norm : A₀ ≤ Subgroup.normalizer (B₀ : Set (Perm (Fin n)))
  X₀ : Subgroup (Perm (Fin n))
  hX₀ : X₀ = A₀ ⊔ B₀
  hX₀card : Nat.card X₀ = 6 * Nat.card B₀

private theorem exists_data_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P} :
    Nonempty (Data_g45j B) := by
  let A₀ : Subgroup (Perm (Fin n)) := fixingSubgroup (Perm (Fin n)) ((B.Δ₀ : Set (Fin n))ᶜ)
  let A₁ : Subgroup (Perm (Fin n)) := fixingSubgroup (Perm (Fin n)) (B.Δ₀ : Set (Fin n))
  obtain ⟨B₀, hB₀⟩ := exists_isSylowOf 2 A₁
  let σ₀ : Perm (Fin n) := Equiv.swap B.a B.b
  have hσ₀A₀ : σ₀ ∈ A₀ := by
    dsimp only [A₀, σ₀]
    exact swap_mem_fixingSubgroup_compl_g45j B.Δ₀
      (by rw [B.hΔ₀]; simp) (by rw [B.hΔ₀]; simp)
  have hσ₀swap : σ₀.IsSwap := by
    dsimp only [σ₀]
    rw [Equiv.Perm.swap_isSwap_iff]
    exact B.hba.symm
  have hσ₀order : orderOf σ₀ = 2 := hσ₀swap.orderOf
  have hA₀A₁ : A₀ ⊓ A₁ = ⊥ := by
    dsimp only [A₀, A₁]
    exact inf_fixingSubgroup_compl_g45j B.Δ₀
  have hB₀disj : A₀ ⊓ B₀ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ A₀ ⊓ A₁ := ⟨hx.1, hB₀.le hx.2⟩
    rwa [hA₀A₁, Subgroup.mem_bot] at hx'
  have hA₀cent : A₀ ≤ Subgroup.centralizer (B₀ : Set (Perm (Fin n))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_of_mem_fixingSubgroup_g45j (s := (B.Δ₀ : Set (Fin n)))
      (hB₀.le hy) hx).eq
  have hA₀norm : A₀ ≤ Subgroup.normalizer (B₀ : Set (Perm (Fin n))) :=
    hA₀cent.trans (Subgroup.centralizer_le_normalizer _)
  let X₀ : Subgroup (Perm (Fin n)) := A₀ ⊔ B₀
  have hA₀card : Nat.card A₀ = 6 := by
    dsimp only [A₀]
    exact card_fixingSubgroup_compl_of_card_g45j B.Δ₀ B.hΔ₀card
  have hX₀card : Nat.card X₀ = 6 * Nat.card B₀ := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B₀ A₀
      hA₀norm (disjoint_iff.mpr hB₀disj).symm
    rw [sup_comm] at h
    rw [h, hA₀card, mul_comm]
  exact ⟨⟨A₀, A₁, B₀, rfl, rfl, hB₀, σ₀, rfl, hσ₀A₀, hσ₀swap, hσ₀order,
    hA₀A₁, hB₀disj, hA₀cent, hA₀norm, X₀, rfl, hX₀card⟩⟩

private structure RData_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P}
    (D : Data_g45j B) where
  R : Subgroup (Perm (Fin n))
  hR : R = D.B₀ ⊔ Subgroup.zpowers D.σ₀
  hR2 : IsPGroup 2 R
  hRcard : Nat.card R = 2 * Nat.card D.B₀
  hRX₀ : R ≤ D.X₀
  hR_sylow : IsSylowOf 2 R D.X₀
  hRX₁ : R ≤ B.X₁

private theorem B₀_normalizes_zpowers_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} :
    D.B₀ ≤ Subgroup.normalizer (Subgroup.zpowers D.σ₀) := by
  intro b hb
  have hcomm : Commute b D.σ₀ :=
    Subgroup.mem_centralizer_iff.mp (D.hA₀cent D.hσ₀A₀) b hb
  have hconj : MulAut.conj b D.σ₀ = D.σ₀ := by
    change b * D.σ₀ * b⁻¹ = D.σ₀
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm' : Commute b⁻¹ D.σ₀ := hcomm.inv_left
  have hconj' : MulAut.conj b⁻¹ D.σ₀ = D.σ₀ := by
    change b⁻¹ * D.σ₀ * (b⁻¹)⁻¹ = D.σ₀
    rw [hcomm'.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hle : Subgroup.zpowers D.σ₀ ≤ (Subgroup.zpowers D.σ₀).comap
        (MulAut.conj b).toMonoidHom := by
      rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      change (MulAut.conj b) D.σ₀ ∈ Subgroup.zpowers D.σ₀
      rw [hconj]
      exact Subgroup.mem_zpowers D.σ₀
    have hx' : (MulAut.conj b) x ∈ Subgroup.zpowers D.σ₀ := hle hx
    simpa only [MulAut.conj_apply, inv_inv] using hx'
  · intro hx
    have hle : Subgroup.zpowers D.σ₀ ≤ (Subgroup.zpowers D.σ₀).comap
        (MulAut.conj b⁻¹).toMonoidHom := by
      rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      change (MulAut.conj b⁻¹) D.σ₀ ∈ Subgroup.zpowers D.σ₀
      rw [hconj']
      exact Subgroup.mem_zpowers D.σ₀
    have hx' : (MulAut.conj b⁻¹) (b * x * b⁻¹) ∈ Subgroup.zpowers D.σ₀ := hle hx
    have hx'' : b⁻¹ * (b * x * b⁻¹) * b ∈ Subgroup.zpowers D.σ₀ := by
      simpa only [MulAut.conj_apply, inv_inv] using hx'
    have hxe : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    rwa [hxe] at hx''

private theorem R_sylow_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P}
    {D : Data_g45j B}
    (hBnorm : D.B₀ ≤ Subgroup.normalizer (Subgroup.zpowers D.σ₀))
    (hBdisj : D.B₀ ⊓ Subgroup.zpowers D.σ₀ = ⊥) :
    IsSylowOf 2 (D.B₀ ⊔ Subgroup.zpowers D.σ₀) D.X₀ := by
  have hzp2 : IsPGroup 2 (Subgroup.zpowers D.σ₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, D.hσ₀order]
    norm_num
  have hR2 : IsPGroup 2
      (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))) :=
    IsPGroup.to_sup_of_normal_right' D.hB₀.isPGroup hzp2 hBnorm
  have hRcard :
      Nat.card (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))) =
        2 * Nat.card D.B₀ := by
    have hd : Disjoint (Subgroup.zpowers D.σ₀) D.B₀ :=
      disjoint_iff.mpr (by rw [inf_comm]; exact hBdisj)
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers D.σ₀) D.B₀ hBnorm hd
    rw [sup_comm] at h
    rw [Nat.card_zpowers, D.hσ₀order] at h
    exact h
  have hRX₀ : D.B₀ ⊔ Subgroup.zpowers D.σ₀ ≤ D.X₀ := by
    rw [D.hX₀]
    refine sup_le le_sup_right ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left D.hσ₀A₀)
  rw [isSylowOf_iff]
  refine ⟨hRX₀, hR2, ?_⟩
  have hBpos : 0 < Nat.card D.B₀ := Nat.card_pos
  have hmul := Subgroup.relIndex_mul_card
    (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))) D.X₀
  rw [inf_eq_left.mpr hRX₀, hRcard, D.hX₀card] at hmul
  have hrel :
      (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))).relIndex D.X₀ = 3 := by
    have h2 :
        (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))).relIndex D.X₀ * 2 = 6 := by
      apply Nat.mul_right_cancel hBpos
      calc
        (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))).relIndex D.X₀ * 2 *
            Nat.card D.B₀
          = (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))).relIndex D.X₀ *
              (2 * Nat.card D.B₀) := by ring
        _ = 6 * Nat.card D.B₀ := hmul
    omega
  rw [hrel]
  norm_num

private theorem R_le_stabilizer_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} :
    D.B₀ ⊔ Subgroup.zpowers D.σ₀ ≤ B.X₁ := by
  have hfΔ₀ : B.f ∈ B.Δ₀ := by rw [B.hΔ₀]; simp
  have hσ₀X₁ : D.σ₀ ∈ B.X₁ := by
    rw [B.hX₁]
    refine (MulAction.mem_stabilizer_iff).mpr ?_
    rw [D.hσ₀]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm B.ha) (Ne.symm B.hbf)
  have hB₀X₁ : D.B₀ ≤ B.X₁ := by
    intro b hb
    have hbA₁ : b ∈ fixingSubgroup (Perm (Fin n)) (B.Δ₀ : Set (Fin n)) := by
      rw [← D.hA₁]
      exact D.hB₀.le hb
    rw [B.hX₁]
    exact (MulAction.mem_stabilizer_iff).mpr (by
      simpa using ((mem_fixingSubgroup_iff (Perm (Fin n))).mp hbA₁) B.f hfΔ₀)
  exact sup_le hB₀X₁ (Subgroup.zpowers_le.mpr hσ₀X₁)

private theorem exists_RData_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P}
    {D : Data_g45j B} : Nonempty (RData_g45j D) := by
  have hBnorm := B₀_normalizes_zpowers_g45j (D := D)
  have hBdisj : D.B₀ ⊓ Subgroup.zpowers D.σ₀ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxA₀ : x ∈ D.A₀ := Subgroup.zpowers_le.mpr D.hσ₀A₀ hx.2
    have hx' : x ∈ D.A₀ ⊓ D.B₀ := ⟨hxA₀, hx.1⟩
    rwa [D.hB₀disj, Subgroup.mem_bot] at hx'
  have hRsylow := R_sylow_g45j (D := D) hBnorm hBdisj
  have hzp2 : IsPGroup 2 (Subgroup.zpowers D.σ₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, D.hσ₀order]
    norm_num
  have hR2 : IsPGroup 2
      (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))) :=
    IsPGroup.to_sup_of_normal_right' D.hB₀.isPGroup hzp2 hBnorm
  have hRcard :
      Nat.card (D.B₀ ⊔ Subgroup.zpowers D.σ₀ : Subgroup (Perm (Fin n))) =
        2 * Nat.card D.B₀ := by
    have hd : Disjoint (Subgroup.zpowers D.σ₀) D.B₀ :=
      disjoint_iff.mpr (by rw [inf_comm]; exact hBdisj)
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers D.σ₀) D.B₀ hBnorm hd
    rw [sup_comm] at h
    rw [Nat.card_zpowers, D.hσ₀order] at h
    exact h
  have hRX₀ : D.B₀ ⊔ Subgroup.zpowers D.σ₀ ≤ D.X₀ := by
    rw [D.hX₀]
    refine sup_le le_sup_right ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left D.hσ₀A₀)
  exact ⟨⟨D.B₀ ⊔ Subgroup.zpowers D.σ₀, rfl, hR2, hRcard, hRX₀, hRsylow,
    R_le_stabilizer_g45j⟩⟩

private structure ConjData_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P}
    {D : Data_g45j B} (R : RData_g45j D) where
  g : Perm (Fin n)
  hgX₁ : g ∈ B.X₁
  hgR : ∀ q ∈ R.R, g * q * g⁻¹ ∈ P
  hgf : g B.f = B.f

private theorem exists_conjData_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P}
    {D : Data_g45j B} (R : RData_g45j D) {hP : IsSylowOf 2 P ⊤} :
    Nonempty (ConjData_g45j R) := by
  obtain ⟨g, hgX₁, hgR⟩ :=
    CFSG.ComponentClassification.GHarris.exists_conj_le_of_isSylowOf
      (K := B.X₁) (P := P) (Q := R.R) (hP.of_le B.hPX₁ le_top) R.hRX₁ R.hR2
  refine ⟨⟨g, hgX₁, hgR, ?_⟩⟩
  have h := hgX₁
  rw [B.hX₁] at h
  simpa using (MulAction.mem_stabilizer_iff.mp h)

private structure X₂Data_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))} {B : Base_g45j P}
    {D : Data_g45j B} {R : RData_g45j D} (C : ConjData_g45j R) where
  Δ : Finset (Fin n)
  X₂ : Subgroup (Perm (Fin n))
  hfΔ : B.f ∈ Δ
  hΔcard : Δ.card = 3
  hgmem : ∀ w : Fin n, w ∈ Δ ↔ C.g⁻¹ w ∈ B.Δ₀
  hX₂map : X₂ = D.X₀.map (MulAut.conj C.g).toMonoidHom
  hX₂split : X₂ = D.A₀.map (MulAut.conj C.g).toMonoidHom ⊔
    D.B₀.map (MulAut.conj C.g).toMonoidHom
  hPinf : IsSylowOf 2 (P ⊓ X₂) X₂
  hX₂ne : X₂ ≠ ⊤
  hX₂notle : ¬ X₂ ≤ B.X₁

private theorem exists_X₂Basic_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} (C : ConjData_g45j R) :
    ∃ (Δ : Finset (Fin n)) (X₂ : Subgroup (Perm (Fin n))),
      B.f ∈ Δ ∧ Δ.card = 3 ∧ (∀ w : Fin n, w ∈ Δ ↔ C.g⁻¹ w ∈ B.Δ₀) ∧
      X₂ = D.X₀.map (MulAut.conj C.g).toMonoidHom ∧
      X₂ = D.A₀.map (MulAut.conj C.g).toMonoidHom ⊔
        D.B₀.map (MulAut.conj C.g).toMonoidHom := by
  let Δ : Finset (Fin n) := B.Δ₀.image C.g
  let X₂ : Subgroup (Perm (Fin n)) :=
    D.X₀.map (MulAut.conj C.g).toMonoidHom
  have hfΔ : B.f ∈ Δ := Finset.mem_image.mpr ⟨B.f, by rw [B.hΔ₀]; simp, C.hgf⟩
  have hΔcard : Δ.card = 3 := by
    dsimp only [Δ]
    rw [Finset.card_image_of_injective _ C.g.injective, B.hΔ₀card]
  have hgmem : ∀ w : Fin n, w ∈ Δ ↔ C.g⁻¹ w ∈ B.Δ₀ := by
    intro w
    dsimp only [Δ]
    rw [Finset.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hw
      exact ⟨C.g⁻¹ w, hw, by simp⟩
  have hX₂map : X₂ = D.X₀.map (MulAut.conj C.g).toMonoidHom := rfl
  have hX₂split : X₂ = D.A₀.map (MulAut.conj C.g).toMonoidHom ⊔
      D.B₀.map (MulAut.conj C.g).toMonoidHom := by
    rw [hX₂map, D.hX₀, Subgroup.map_sup]
  exact ⟨Δ, X₂, hfΔ, hΔcard, hgmem, hX₂map, hX₂split⟩

private theorem Pinf_X₂_sylow_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    {X₂ : Subgroup (Perm (Fin n))}
    (hX₂ : X₂ = D.A₀.map (MulAut.conj C.g).toMonoidHom ⊔
      D.B₀.map (MulAut.conj C.g).toMonoidHom) {hP : IsSylowOf 2 P ⊤} :
    IsSylowOf 2 (P ⊓ X₂) X₂ := by
  have hmapX₀ : D.X₀.map (MulAut.conj C.g).toMonoidHom = X₂ := by
    rw [D.hX₀, Subgroup.map_sup, ← hX₂]
  have hR₂_sylow : IsSylowOf 2 (R.R.map (MulAut.conj C.g).toMonoidHom) X₂ := by
    have h := CFSG.GroupTheory.isSylowOf_map_conj R.hR_sylow C.g
    rwa [hmapX₀] at h
  have hR₂P : R.R.map (MulAut.conj C.g).toMonoidHom ≤ P := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz
    change C.g * r * C.g⁻¹ ∈ P
    exact C.hgR r hr
  have heq : P ⊓ X₂ = R.R.map (MulAut.conj C.g).toMonoidHom := by
    refine hR₂_sylow.eq_of_le (le_inf hR₂P ?_) inf_le_right ?_
    · rw [← hmapX₀]
      exact Subgroup.map_mono R.hRX₀
    exact hP.isPGroup.to_le inf_le_left
  rw [heq]
  exact hR₂_sylow

private theorem X₂_ne_top_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    {Δ : Finset (Fin n)} {X₂ : Subgroup (Perm (Fin n))}
    (hΔcard : Δ.card = 3)
    (hgmem : ∀ w : Fin n, w ∈ Δ ↔ C.g⁻¹ w ∈ B.Δ₀)
    (hX₂map : X₂ = D.X₀.map (MulAut.conj C.g).toMonoidHom)
    (h5 : 5 ≤ Fintype.card (Fin n)) :
    X₂ ≠ ⊤ := by
  obtain ⟨y, -, hyΔ⟩ : ∃ y ∈ (Finset.univ : Finset (Fin n)), y ∉ Δ :=
    Finset.exists_mem_notMem_of_card_lt_card (by
      rw [hΔcard, Finset.card_univ]
      exact lt_of_lt_of_le (by norm_num) h5)
  intro htop
  have hmem : Equiv.swap B.f y ∈ X₂ := by rw [htop]; exact Subgroup.mem_top _
  rw [hX₂map] at hmem
  obtain ⟨u, huX₀, hu_eq⟩ := Subgroup.mem_map.mp hmem
  have hfΔ₀ : B.f ∈ B.Δ₀ := by rw [B.hΔ₀]; simp
  have hzΔ₀ : C.g⁻¹ y ∉ B.Δ₀ := fun h => hyΔ ((hgmem y).mpr h)
  have hu_apply : u B.f = C.g⁻¹ y := by
    have h1 : C.g (u B.f) = y := by
      calc C.g (u B.f) = (C.g * u * C.g⁻¹) (C.g B.f) := by
            rw [Perm.mul_apply, Perm.mul_apply]
            exact (congrArg (fun z => C.g (u z)) (Equiv.symm_apply_apply C.g B.f)).symm
        _ = (MulAut.conj C.g u) (C.g B.f) := by rw [MulAut.conj_apply]
        _ = (Equiv.swap B.f y) B.f := by
            simpa [C.hgf] using congrArg (fun σ : Perm (Fin n) => σ (C.g B.f)) hu_eq
        _ = y := Equiv.swap_apply_left B.f y
    calc u B.f = C.g⁻¹ (C.g (u B.f)) := (Equiv.symm_apply_apply C.g (u B.f)).symm
      _ = C.g⁻¹ y := by rw [h1]
  have h := huX₀
  rw [D.hX₀] at h
  change u ∈ (↑(D.A₀ ⊔ D.B₀) : Set (Perm (Fin n))) at h
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D.A₀ D.B₀ D.hA₀norm] at h
  obtain ⟨aa, haaA₀, bb, hbbB₀, hab⟩ := Set.mem_mul.mp h
  have hbbf : bb B.f = B.f := by
    have hbA₁ : bb ∈ fixingSubgroup (Perm (Fin n)) (B.Δ₀ : Set (Fin n)) := by
      rw [← D.hA₁]
      exact D.hB₀.le hbbB₀
    exact ((mem_fixingSubgroup_iff (Perm (Fin n))).mp hbA₁) B.f hfΔ₀
  have haaf : aa B.f ∈ B.Δ₀ := by
    have haA₀ : aa ∈ fixingSubgroup (Perm (Fin n)) ((B.Δ₀ : Set (Fin n))ᶜ) := by
      rw [← D.hA₀]
      exact haaA₀
    exact apply_mem_of_mem_fixingSubgroup_compl_g45j haA₀ hfΔ₀
  have : u B.f ∈ B.Δ₀ := by
    rw [← hab, Perm.mul_apply, hbbf]
    exact haaf
  rw [hu_apply] at this
  exact hzΔ₀ this

private theorem X₂_not_le_X₁_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    {X₂ : Subgroup (Perm (Fin n))}
    (hX₂split : X₂ = D.A₀.map (MulAut.conj C.g).toMonoidHom ⊔
      D.B₀.map (MulAut.conj C.g).toMonoidHom) :
    ¬ X₂ ≤ B.X₁ := by
  have hga_ne_f : C.g B.a ≠ B.f := by
    intro h
    exact B.ha (C.g.injective (h.trans C.hgf.symm))
  intro hle
  have hmemA : Equiv.swap B.f (C.g B.a) ∈
      D.A₀.map (MulAut.conj C.g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨Equiv.swap B.f B.a, ?_, ?_⟩
    · have haA₀ : Equiv.swap B.f B.a ∈
          fixingSubgroup (Perm (Fin n)) ((B.Δ₀ : Set (Fin n))ᶜ) :=
        swap_mem_fixingSubgroup_compl_g45j B.Δ₀
          (by rw [B.hΔ₀]; simp) (by rw [B.hΔ₀]; simp)
      simpa only [D.hA₀] using haA₀
    · change C.g * Equiv.swap B.f B.a * C.g⁻¹ = Equiv.swap B.f (C.g B.a)
      rw [← Equiv.swap_apply_apply C.g B.f B.a, C.hgf]
  have hmem : Equiv.swap B.f (C.g B.a) ∈ X₂ := by
    rw [hX₂split]
    exact Subgroup.mem_sup_left hmemA
  have hnot := hle hmem
  rw [B.hX₁] at hnot
  have hval : Equiv.swap B.f (C.g B.a) B.f = B.f := by
    simpa using (MulAction.mem_stabilizer_iff.mp hnot)
  rw [Equiv.swap_apply_left] at hval
  exact hga_ne_f hval

private theorem exists_X₂Data_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} (C : ConjData_g45j R)
    {hP : IsSylowOf 2 P ⊤} (h5 : 5 ≤ n) : Nonempty (X₂Data_g45j C) := by
  obtain ⟨Δ, X₂, hfΔ, hΔcard, hgmem, hX₂map, hX₂split⟩ := exists_X₂Basic_g45j C
  have hPinf := Pinf_X₂_sylow_g45j (C := C) (X₂ := X₂) hX₂split (hP := hP)
  have h5' : 5 ≤ Fintype.card (Fin n) := by simpa using h5
  have hX₂ne := X₂_ne_top_g45j (C := C) (Δ := Δ) (X₂ := X₂) hΔcard hgmem hX₂map h5'
  have hX₂notle := X₂_not_le_X₁_g45j (C := C) (X₂ := X₂) hX₂split
  exact ⟨⟨Δ, X₂, hfΔ, hΔcard, hgmem, hX₂map, hX₂split, hPinf, hX₂ne, hX₂notle⟩⟩

private theorem one_in_one_out_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    {X : X₂Data_g45j C} {hP : IsSylowOf 2 P ⊤}
    {u v : Fin n} (huΔ : u ∈ X.Δ) (hvΔ : v ∉ X.Δ) (huf : u ≠ B.f)
    (huvP : Equiv.swap u v ∈ P) : Equiv.swap u v ∈ X.X₂ := by
  have hPg2 : IsPGroup 2 (P.map (MulAut.conj C.g⁻¹).toMonoidHom) :=
    hP.isPGroup.map (MulAut.conj C.g⁻¹).toMonoidHom
  have hσ₀Pg : D.σ₀ ∈ P.map (MulAut.conj C.g⁻¹).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨MulAut.conj C.g D.σ₀, ?_, ?_⟩
    · refine C.hgR D.σ₀ ?_
      rw [R.hR]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.σ₀)
    · change C.g⁻¹ * (C.g * D.σ₀ * C.g⁻¹) * C.g = D.σ₀
      group
  have hu₀ : C.g⁻¹ u ∈ B.Δ₀ := (X.hgmem u).mp huΔ
  have hu₀_ne_f : C.g⁻¹ u ≠ B.f := by
    intro h
    have h2 : C.g (C.g⁻¹ u) = C.g B.f := congrArg C.g h
    have h3 : u = C.g B.f := (Equiv.apply_symm_apply C.g u).symm.trans h2
    rw [C.hgf] at h3
    exact huf h3
  have hu₀_eq : C.g⁻¹ u = B.a ∨ C.g⁻¹ u = B.b := by
    have hmem := hu₀
    rw [B.hΔ₀] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd h hu₀_ne_f
    · exact Or.inl h
    · exact Or.inr h
  have hv₀ : C.g⁻¹ v ∉ B.Δ₀ := fun h => hvΔ ((X.hgmem v).mpr h)
  have haw : B.a ≠ C.g⁻¹ v := fun h => hv₀ (h ▸ (by rw [B.hΔ₀]; simp))
  have hbw : B.b ≠ C.g⁻¹ v := fun h => hv₀ (h ▸ (by rw [B.hΔ₀]; simp))
  have ht_eq : MulAut.conj C.g⁻¹ (Equiv.swap u v) =
      Equiv.swap (C.g⁻¹ u) (C.g⁻¹ v) := by
    rw [MulAut.conj_apply, ← Equiv.swap_apply_apply C.g⁻¹ u v]
  have htPg : MulAut.conj C.g⁻¹ (Equiv.swap u v) ∈
      P.map (MulAut.conj C.g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ huvP
  have hprod : D.σ₀ * MulAut.conj C.g⁻¹ (Equiv.swap u v) ∈
      P.map (MulAut.conj C.g⁻¹).toMonoidHom :=
    Subgroup.mul_mem _ hσ₀Pg htPg
  have h3 : 3 ∣ orderOf (D.σ₀ * MulAut.conj C.g⁻¹ (Equiv.swap u v)) := by
    rw [ht_eq]
    rcases hu₀_eq with h | h
    · rw [h]
      simpa only [D.hσ₀] using three_dvd_swap_mul_swap_g45j B.hba.symm haw hbw
    · rw [h]
      simpa only [D.hσ₀] using three_dvd_swap_mul_swap'_g45j B.hba.symm hbw haw
  exact absurd h3 (not_three_dvd_orderOf_g45j hPg2 hprod)

private theorem swap_two_in_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    {X : X₂Data_g45j C} {x y : Fin n} (hxΔ : x ∈ X.Δ) (hyΔ : y ∈ X.Δ) :
    Equiv.swap x y ∈ X.X₂ := by
  have hxA₀ : MulAut.conj C.g⁻¹ (Equiv.swap x y) ∈ D.A₀ := by
    have haA₀ : MulAut.conj C.g⁻¹ (Equiv.swap x y) ∈
        fixingSubgroup (Perm (Fin n)) ((B.Δ₀ : Set (Fin n))ᶜ) := by
      rw [mem_fixingSubgroup_iff]
      have ht_eq : MulAut.conj C.g⁻¹ (Equiv.swap x y) =
          Equiv.swap (C.g⁻¹ x) (C.g⁻¹ y) := by
        rw [MulAut.conj_apply, ← Equiv.swap_apply_apply C.g⁻¹ x y]
      rw [ht_eq]
      intro z hz
      exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hz (h ▸ (X.hgmem x).mp hxΔ))
        (fun h => hz (h ▸ (X.hgmem y).mp hyΔ))
    simpa only [D.hA₀] using haA₀
  have hxmap : Equiv.swap x y ∈ D.A₀.map (MulAut.conj C.g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨MulAut.conj C.g⁻¹ (Equiv.swap x y), hxA₀, ?_⟩
    change C.g * (C.g⁻¹ * Equiv.swap x y * C.g) * C.g⁻¹ = Equiv.swap x y
    group
  rw [X.hX₂split]
  exact Subgroup.mem_sup_left hxmap

private theorem swap_two_out_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    {X : X₂Data_g45j C} {x y : Fin n} (hxΔ : x ∉ X.Δ) (hyΔ : y ∉ X.Δ)
    {hP : IsSylowOf 2 P ⊤} (hxyP : Equiv.swap x y ∈ P) :
    Equiv.swap x y ∈ X.X₂ := by
  have hPg2 : IsPGroup 2 (P.map (MulAut.conj C.g⁻¹).toMonoidHom) :=
    hP.isPGroup.map (MulAut.conj C.g⁻¹).toMonoidHom
  have ht_eq : MulAut.conj C.g⁻¹ (Equiv.swap x y) =
      Equiv.swap (C.g⁻¹ x) (C.g⁻¹ y) := by
    rw [MulAut.conj_apply, ← Equiv.swap_apply_apply C.g⁻¹ x y]
  have hxA₁ : MulAut.conj C.g⁻¹ (Equiv.swap x y) ∈ D.A₁ := by
    have haA₁ : MulAut.conj C.g⁻¹ (Equiv.swap x y) ∈
        fixingSubgroup (Perm (Fin n)) (B.Δ₀ : Set (Fin n)) := by
      rw [mem_fixingSubgroup_iff]
      rw [ht_eq]
      have hx₀ : C.g⁻¹ x ∉ B.Δ₀ := fun h => hxΔ ((X.hgmem x).mpr h)
      have hy₀ : C.g⁻¹ y ∉ B.Δ₀ := fun h => hyΔ ((X.hgmem y).mpr h)
      intro z hz
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hx₀ (h ▸ hz))
        (fun h => hy₀ (h ▸ hz))
    simpa only [D.hA₁] using haA₁
  have hxPg : MulAut.conj C.g⁻¹ (Equiv.swap x y) ∈
      P.map (MulAut.conj C.g⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hxyP
  let Q : Subgroup (Perm (Fin n)) :=
    D.A₁ ⊓ P.map (MulAut.conj C.g⁻¹).toMonoidHom
  have hQ2 : IsPGroup 2 Q := hPg2.to_le inf_le_right
  have hB₀le : D.B₀ ≤ Q := by
    intro b hb
    refine ⟨D.hB₀.le hb, ?_⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj C.g b, ?_, ?_⟩
    · refine C.hgR b ?_
      rw [R.hR]
      exact Subgroup.mem_sup_left hb
    · change C.g⁻¹ * (C.g * b * C.g⁻¹) * C.g = b
      group
  have heq : Q = D.B₀ := D.hB₀.eq_of_le hB₀le inf_le_left hQ2
  have hxB₀ : MulAut.conj C.g⁻¹ (Equiv.swap x y) ∈ D.B₀ := by
    rw [← heq]
    exact ⟨hxA₁, hxPg⟩
  have hxmap : Equiv.swap x y ∈ D.B₀.map (MulAut.conj C.g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨MulAut.conj C.g⁻¹ (Equiv.swap x y), hxB₀, ?_⟩
    change C.g * (C.g⁻¹ * Equiv.swap x y * C.g) * C.g⁻¹ = Equiv.swap x y
    group
  rw [X.hX₂split]
  exact Subgroup.mem_sup_right hxmap

private theorem swap_mem_X₂_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    (X : X₂Data_g45j C) {hP : IsSylowOf 2 P ⊤} :
    ∀ τ ∈ P, τ.IsSwap → τ ∈ X.X₂ := by
  intro τ hτP hτswap
  obtain ⟨x, y, hxy, rfl⟩ := hτswap
  have hfix : Equiv.swap x y B.f = B.f := B.hfP _ hτP
  have hxf : x ≠ B.f := by
    intro h
    rw [h, Equiv.swap_apply_left] at hfix
    exact hxy (h.trans hfix.symm)
  have hyf : y ≠ B.f := by
    intro h
    rw [h, Equiv.swap_apply_right] at hfix
    exact hxy (hfix.trans h.symm)
  by_cases hxΔ : x ∈ X.Δ <;> by_cases hyΔ : y ∈ X.Δ
  · exact swap_two_in_g45j hxΔ hyΔ
  · exact one_in_one_out_g45j (hP := hP) hxΔ hyΔ hxf hτP
  · rw [Equiv.swap_comm]
    exact one_in_one_out_g45j (hP := hP) hyΔ hxΔ hyf (by rwa [Equiv.swap_comm y x])
  · exact swap_two_out_g45j (hP := hP) hxΔ hyΔ hτP

private theorem sup_eq_top_g45j {n : ℕ} {P : Subgroup (Perm (Fin n))}
    {B : Base_g45j P} {D : Data_g45j B} {R : RData_g45j D} {C : ConjData_g45j R}
    (X : X₂Data_g45j C) : B.X₁ ⊔ X.X₂ = ⊤ := by
  have hlt : B.X₁ < B.X₁ ⊔ X.X₂ := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    exact X.hX₂notle fun x hx => heq ▸ Subgroup.mem_sup_right hx
  exact B.hX₁coatom.lt_iff.mp hlt

theorem exists_sup_eq_top_of_isSylowOf {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n)
    {P : Subgroup (Perm (Fin n))} (hP : IsSylowOf 2 P ⊤) :
    ∃ X₁ X₂ : Subgroup (Perm (Fin n)), X₁ ≠ ⊤ ∧ X₂ ≠ ⊤ ∧ X₁ ⊔ X₂ = ⊤ ∧
      IsSylowOf 2 (P ⊓ X₁) X₁ ∧ IsSylowOf 2 (P ⊓ X₂) X₂ ∧
      ∀ τ ∈ P, τ.IsSwap → τ ∈ X₁ ⊓ X₂ := by
  classical
  obtain ⟨B⟩ := exists_base_g45j hn h5 hP
  obtain ⟨D⟩ := exists_data_g45j (B := B)
  obtain ⟨R⟩ := exists_RData_g45j (D := D)
  obtain ⟨C⟩ := exists_conjData_g45j (R := R) (hP := hP)
  obtain ⟨X⟩ := exists_X₂Data_g45j (C := C) (hP := hP) h5
  have htrans := swap_mem_X₂_g45j (X := X) (hP := hP)
  have hsup := sup_eq_top_g45j (X := X)
  refine ⟨B.X₁, X.X₂, B.hX₁coatom.ne_top, X.hX₂ne, hsup, ?_, X.hPinf, ?_⟩
  · rw [inf_eq_left.mpr B.hPX₁]
    exact hP.of_le B.hPX₁ le_top
  · intro τ hτP hτswap
    exact ⟨B.hPX₁ hτP, htrans τ hτP hτswap⟩

end CFSG.GroupTheory.PermSylowTwo
