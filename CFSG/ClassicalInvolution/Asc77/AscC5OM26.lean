module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM24
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import CFSG.ClassicalInvolution.Asc77.AscC25W15
public import CFSG.ClassicalInvolution.Asc77.AscC5O5M8
public import CFSG.ClassicalInvolution.Asc77.AscC5OM23
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open scoped Matrix MatrixGroups

section TwinIso

variable {M S H₁ H₂ : Type} [Group M] [Group S] [Group H₁] [Group H₂]

theorem exists_twin_iso [Finite S] (π₁ : M →* H₁) (π₂ : M →* H₂) (hker : π₁.ker = π₂.ker)
    (L : Subgroup M) (f₁ : S →* H₁) (f₂ : S →* H₂) (hf₁ : Function.Injective f₁)
    (hf₂ : Function.Injective f₂) (h₁ : L.map π₁ = f₁.range) (h₂ : L.map π₂ = f₂.range) :
    ∃ θ : MulAut S, ∀ (m : M) (b : S), π₁ m = f₁ b → π₂ m = f₂ (θ b) := by
  classical
  have hm : ∀ b : S, ∃ m ∈ L, π₁ m = f₁ b := fun b => by
    have : f₁ b ∈ L.map π₁ := h₁ ▸ ⟨b, rfl⟩
    obtain ⟨m, hm, e⟩ := this
    exact ⟨m, hm, e⟩
  choose m hmL hmb using hm
  have hc : ∀ b : S, ∃ c : S, f₂ c = π₂ (m b) := fun b => by
    have : π₂ (m b) ∈ f₂.range := h₂ ▸ ⟨m b, hmL b, rfl⟩
    exact this
  choose t ht using hc
  have key : ∀ (x : M) (b : S), π₁ x = f₁ b → π₂ x = f₂ (t b) := fun x b hx => by
    have h1 : (m b)⁻¹ * x ∈ π₂.ker := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hx, hmb, inv_mul_cancel]
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1, ht]
  have hmul : ∀ b b' : S, t (b * b') = t b * t b' := fun b b' => by
    apply hf₂
    rw [map_mul, ← key (m b * m b') (b * b') (by rw [map_mul, hmb, hmb, map_mul]), map_mul,
      ht, ht]
  have hinj : Function.Injective t := fun b b' hbb => by
    apply hf₁
    have h1 : (m b)⁻¹ * m b' ∈ π₁.ker := by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, ← ht, ← ht, hbb, inv_mul_cancel]
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← hmb, ← hmb, h1]
  let θ : MulAut S := MulEquiv.ofBijective (MonoidHom.mk' t hmul)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨θ, fun x b hx => key x b hx⟩

end TwinIso

variable {F : Type} [Field F]

section L01

theorem exists_mul_of_mem_sup_L (h2 : (2 : F) ≠ 0) {x : StatedSp 2 F}
    (hx : x ∈ longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1) :
    ∃ a ∈ longRootSp2 F 2 0, ∃ b ∈ longRootSp2 F 2 1, x = a * b := by
  have hle : longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1 ≤
      Subgroup.centralizer ({longInv F 2 0} : Set (StatedSp 2 F)) := by
    refine sup_le ?_ ?_ <;> intro y hy <;> rw [Subgroup.mem_centralizer_singleton_iff] <;>
      exact (longInv_comm_L 0 _ hy).symm
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute_longInv h2 0 hc
  rw [complGroup_longInv_two h2] at hb
  exact ⟨a, ha, b, hb, rfl⟩

theorem conj_mem_L_of_mem_sup (h2 : (2 : F) ≠ 0) (k : Fin 2) {x r : StatedSp 2 F}
    (hx : x ∈ longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1) (hr : r ∈ longRootSp2 F 2 k) :
    x * r * x⁻¹ ∈ longRootSp2 F 2 k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_L h2 hx
  fin_cases k
  · have e : b * r = r * b := (commute_L 0 hr hb).symm
    have : a * b * r * (a * b)⁻¹ = a * r * a⁻¹ := by
      calc a * b * r * (a * b)⁻¹ = a * (b * r) * b⁻¹ * a⁻¹ := by group
        _ = a * r * a⁻¹ := by rw [e]; group
    rw [this]
    exact mul_mem (mul_mem ha hr) (inv_mem ha)
  · have hbr : b * r * b⁻¹ ∈ longRootSp2 F 2 1 := mul_mem (mul_mem hb hr) (inv_mem hb)
    have e : a * (b * r * b⁻¹) = (b * r * b⁻¹) * a := commute_L 0 ha hbr
    have : a * b * r * (a * b)⁻¹ = b * r * b⁻¹ := by
      calc a * b * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
        _ = b * r * b⁻¹ := by rw [e]; group
    rw [this]
    exact hbr

theorem eq_of_mem_center_L (k : Fin 2) {a : StatedSp 2 F} (ha : a ∈ longRootSp2 F 2 k)
    (hc : ∀ r ∈ longRootSp2 F 2 k, a * r = r * a) : a = 1 ∨ a = longInv F 2 k := by
  obtain ⟨a₀, rfl⟩ := ha
  have hz : a₀ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact longBlock_injective k (by rw [map_mul, map_mul]; exact (hc _ ⟨g, rfl⟩).symm)
  obtain ⟨u, hu, hua⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hu2 : u ^ 2 = 1 := by simpa using hu
  rcases sq_eq_one_iff.mp hu2 with rfl | rfl
  · left
    have : a₀ = 1 := Subtype.ext (by rw [← hua]; simp)
    rw [this, map_one]
  · right
    have : a₀ = -1 := Subtype.ext (by
      rw [← hua, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      by_cases hij : i = j <;> simp [hij])
    rw [this]
    rfl

end L01

section Basics

theorem negOne_not_mem_L (h2 : (2 : F) ≠ 0) (k : Fin 2) : negOne F ∉ longRootSp2 F 2 k := by
  intro h
  apply longInv_rev_not_mem h2 k
  rw [longInv_rev_eq]
  exact mul_mem h (longInv_mem k)

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}

namespace Frame

variable (fr : Frame F Y Φ A A' z')
include fr

theorem map_sup_L : (longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1).map fr.ψ = A ⊔ A' := by
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) fr.hA.symm fr.hA'.symm

theorem injOn_L (h2 : (2 : F) ≠ 0) (k : Fin 2) {r s : StatedSp 2 F}
    (hr : r ∈ longRootSp2 F 2 k) (hs : s ∈ longRootSp2 F 2 k) (h : fr.ψ r = fr.ψ s) : r = s := by
  rcases fr.lift_eq_iff.mp h with h' | h'
  · exact h'
  · exfalso
    apply negOne_not_mem_L h2 k
    have : negOne F = s⁻¹ * r := by rw [h']; group
    rw [this]
    exact mul_mem (inv_mem hs) hr


end Frame

end Basics

section OddNormal

variable [Finite F]

theorem eq_bot_of_odd_normal_L (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) (k : Fin 2)
    {K : Subgroup (StatedSp 2 F)} (hK : K ≤ longRootSp2 F 2 k)
    (hnorm : ∀ x ∈ K, ∀ r ∈ longRootSp2 F 2 k, r * x * r⁻¹ ∈ K) (hodd : Odd (Nat.card K)) :
    K = ⊥ := by
  set e := longBlock F 2 k with he
  have hinj : Function.Injective e := longBlock_injective k
  set K' := K.comap e with hK'
  have hmap : K'.map e = K := by
    rw [hK', Subgroup.map_comap_eq, ← longRootSp2, inf_eq_right.mpr hK]
  have hnormal : K'.Normal := ⟨fun x hx g => by
    change e (g * x * g⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ hx _ ⟨g, rfl⟩⟩
  have hodd' : Odd (Nat.card K') := by
    rw [← hmap, Subgroup.card_map_of_injective hinj] at hodd
    exact hodd
  have hle : K' ≤ classicalInvolutionOddCore SL(2, F) := le_sSup ⟨hnormal, hodd'⟩
  rw [CFSG.ClassicalInvolution.ModelFacts.LinearAut.oddCore_sl2_eq_bot h2 h4, le_bot_iff] at hle
  rw [← hmap, hle, Subgroup.map_bot]

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}

namespace Frame

variable (fr : Frame F Y Φ A A' z')
include fr

theorem comm_of_odd_normal (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {N : Subgroup Y} (hN : N ≤ A ⊔ A') (hnorm : ∀ n ∈ N, ∀ r ∈ A ⊔ A', r * n * r⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) (k : Fin 2) {n : Y} (hn : n ∈ N) {r : StatedSp 2 F}
    (hr : r ∈ longRootSp2 F 2 k) : n * fr.ψ r = fr.ψ r * n := by
  have hLk : ∀ x ∈ longRootSp2 F 2 k, fr.ψ x ∈ A ⊔ A' := fun x hx => by
    rw [← fr.map_sup_L]
    refine ⟨x, ?_, rfl⟩
    fin_cases k
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  set K := longRootSp2 F 2 k ⊓ N.comap fr.ψ with hK
  have hKnorm : ∀ x ∈ K, ∀ s ∈ longRootSp2 F 2 k, s * x * s⁻¹ ∈ K := fun x hx s hs => by
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨mul_mem (mul_mem hs hx.1) (inv_mem hs), ?_⟩
    change fr.ψ (s * x * s⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ hx.2 _ (hLk s hs)
  let f : K →* N := (fr.ψ.comp K.subtype).codRestrict N (fun x => (Subgroup.mem_inf.mp x.2).2)
  have hf : Function.Injective f := fun x y hxy => by
    have e : fr.ψ x = fr.ψ y := congrArg Subtype.val hxy
    exact Subtype.ext (fr.injOn_L h2 k (Subgroup.mem_inf.mp x.2).1 (Subgroup.mem_inf.mp y.2).1 e)
  have hKodd : Odd (Nat.card K) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective f hf)
  have hK0 : K = ⊥ := eq_bot_of_odd_normal_L h2 h4 k inf_le_left hKnorm hKodd
  have hnA : n ∈ (longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1).map fr.ψ := by
    rw [fr.map_sup_L]
    exact hN hn
  obtain ⟨x, hx, rfl⟩ := hnA
  have hc : x * r * x⁻¹ * r⁻¹ ∈ K := by
    rw [Subgroup.mem_inf]
    refine ⟨mul_mem (conj_mem_L_of_mem_sup h2 k hx hr) (inv_mem hr), ?_⟩
    change fr.ψ (x * r * x⁻¹ * r⁻¹) ∈ N
    have e : fr.ψ (x * r * x⁻¹ * r⁻¹) =
        fr.ψ x * (fr.ψ r * (fr.ψ x)⁻¹ * (fr.ψ r)⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      group
    rw [e]
    exact mul_mem hn (hnorm _ (inv_mem hn) _ (hLk r hr))
  rw [hK0, Subgroup.mem_bot] at hc
  have hxr : x * r = r * x := by
    calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
      _ = r * x := by rw [hc, one_mul]
  rw [← map_mul, ← map_mul, hxr]

theorem eq_one_of_odd_normal (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {N : Subgroup Y} (hN : N ≤ A ⊔ A') (hnorm : ∀ n ∈ N, ∀ r ∈ A ⊔ A', r * n * r⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {n : Y} (hn : n ∈ N) : n = 1 := by
  have hnA : n ∈ (longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1).map fr.ψ := by
    rw [fr.map_sup_L]
    exact hN hn
  obtain ⟨x, hx, rfl⟩ := hnA
  have hxc : ∀ (k : Fin 2), ∀ r ∈ longRootSp2 F 2 k, x * r = r * x := by
    intro k r hr
    have : Group.IsPerfect (longRootSp2 F 2 k) :=
      (isClassicalSL2_longRootSp2 h2 k).isPerfect h4
    have key := eq_of_central_ratio (longRootSp2 F 2 k) (MulAut.conj x).toMonoidHom
      (fun s hs => by
        have e := fr.comm_of_odd_normal h2 h4 hN hnorm hodd k hn hs
        have e' : fr.ψ (x * s * x⁻¹) = fr.ψ s := by
          rw [map_mul, map_mul, map_inv, e]
          group
        rcases fr.lift_eq_iff.mp e' with h | h
        · change x * s * x⁻¹ * s⁻¹ ∈ _
          rw [h, mul_inv_cancel]
          exact one_mem _
        · change x * s * x⁻¹ * s⁻¹ ∈ _
          have e2 : s * negOne F * s⁻¹ = negOne F := by
            rw [Subgroup.mem_center_iff.mp negOne_mem_center s]
            group
          rw [h, e2]
          exact negOne_mem_center) r hr
    change x * r * x⁻¹ = r at key
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [key]
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_L h2 hx
  have hac : ∀ r ∈ longRootSp2 F 2 0, a * r = r * a := fun r hr => by
    have e1 := hxc 0 r hr
    have e2 : b * r = r * b := (commute_L 0 hr hb).symm
    calc a * r = a * b * r * b⁻¹ := by rw [mul_assoc a b r, e2]; group
      _ = r * (a * b) * b⁻¹ := by rw [e1]
      _ = r * a := by group
  have hbc : ∀ r ∈ longRootSp2 F 2 1, b * r = r * b := fun r hr => by
    have e1 := hxc 1 r hr
    have e2 : a * r = r * a := commute_L 0 ha hr
    calc b * r = a⁻¹ * (a * b * r) := by group
      _ = a⁻¹ * (r * (a * b)) := by rw [e1]
      _ = a⁻¹ * (a * r) * b := by rw [e2]; group
      _ = r * b := by group
  have hz1 : fr.ψ (longInv F 2 0) ≠ 1 := by
    intro h
    rw [← MonoidHom.mem_ker, fr.ker, mem_spScalars_iff] at h
    rcases h with h | h
    · exact longInv_ne_one h2 0 h
    · exact negOne_not_mem_L h2 0 (h ▸ longInv_mem 0)
  have hz2 : fr.ψ (longInv F 2 0) * fr.ψ (longInv F 2 0) = 1 := by
    rw [← map_mul, longInv_mul_self, map_one]
  have hzN : fr.ψ (a * b) = fr.ψ (longInv F 2 0) → False := fun h => by
    have hmem : fr.ψ (longInv F 2 0) ∈ N := h ▸ hn
    have hord : orderOf (fr.ψ (longInv F 2 0)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    have hdvd : orderOf (fr.ψ (longInv F 2 0)) ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨_, hmem⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  rcases eq_of_mem_center_L 0 ha hac with rfl | rfl <;>
    rcases eq_of_mem_center_L 1 hb hbc with rfl | rfl
  · rw [mul_one, map_one]
  · exfalso
    apply hzN
    rw [one_mul, fr.ψ_longInv_one, ← fr.hz]
  · exfalso
    exact hzN (by rw [mul_one])
  · rw [show longInv F 2 0 * longInv F 2 1 = negOne F from (negOne_eq_longInv_mul 0).symm,
      fr.ψ_negOne]

theorem ker_le_ker (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {M Y' : Type} [Group M]
    [Group Y'] (π₁ : M →* Y') (π₂ : M →* Y) (hrange : π₂.range = A ⊔ A')
    (hodd : Odd (Nat.card π₁.ker)) : π₁.ker ≤ π₂.ker := by
  set N := π₁.ker.map π₂ with hNdef
  have hN : N ≤ A ⊔ A' := by
    rw [← hrange, hNdef]
    exact Subgroup.map_le_range _ _
  have hnorm : ∀ n ∈ N, ∀ r ∈ A ⊔ A', r * n * r⁻¹ ∈ N := by
    rintro _ ⟨k, hk, rfl⟩ r hr
    rw [← hrange] at hr
    obtain ⟨m, rfl⟩ := hr
    refine ⟨m * k * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (inferInstance : π₁.ker.Normal).conj_mem k hk m
  have hoddN : Odd (Nat.card N) := Odd.of_dvd_nat hodd (Subgroup.card_map_dvd π₁.ker π₂)
  intro k hk
  rw [MonoidHom.mem_ker]
  exact fr.eq_one_of_odd_normal h2 h4 hN hnorm hoddN ⟨k, hk, rfl⟩

end Frame

end OddNormal

end CFSG.ClassicalInvolution.Asc77.C5O.M
