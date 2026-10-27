module

public import CFSG.GH74.GLS.SP.Pre
public import CFSG.GH74.BNPair.RootCalc
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

universe u v

section Image

variable {X : Type u} {Y : Type v} [Group X] [Group Y] (π : X →* Y) {B N : Subgroup X}

theorem map_inf_map_of_ker_le (hker : π.ker ≤ B) :
    B.map π ⊓ N.map π = (B ⊓ N).map π := by
  refine le_antisymm ?_ (Subgroup.map_inf_le _ _ _)
  rintro _ ⟨⟨b, hb, rfl⟩, ⟨m, hm, hbm⟩⟩
  have hk : b⁻¹ * m ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbm, inv_mul_cancel]
  have hmB : m ∈ B := by
    have h := B.mul_mem hb (hker hk)
    rwa [mul_inv_cancel_left] at h
  exact ⟨m, ⟨hmB, hm⟩, hbm⟩

@[expose] def restrictN (N : Subgroup X) : N →* N.map π := π.subgroupMap N

@[simp] theorem coe_restrictN (n : N) : ((restrictN π N n : N.map π) : Y) = π (n : X) := rfl

theorem restrictN_surjective : Function.Surjective (restrictN π N) := π.subgroupMap_surjective N

theorem cartan_map (hker : π.ker ≤ B) :
    cartan (B.map π) (N.map π) = (cartan B N).map (restrictN π N) := by
  ext y
  rw [Subgroup.mem_subgroupOf, map_inf_map_of_ker_le π hker, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hy⟩
    refine ⟨⟨h, hh.2⟩, ?_, Subtype.ext hy⟩
    rw [cartan, Subgroup.mem_subgroupOf]
    exact hh
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(n : X), hn, rfl⟩

theorem cartan_map_normal [(cartan B N).Normal] (hker : π.ker ≤ B) :
    (cartan (B.map π) (N.map π)).Normal := by
  rw [cartan_map π hker]
  exact Subgroup.Normal.map inferInstance _ (restrictN_surjective π)

theorem cartan_le_comap (hker : π.ker ≤ B) :
    cartan B N ≤ (cartan (B.map π) (N.map π)).comap (restrictN π N) := by
  rw [cartan_map π hker]
  exact Subgroup.le_comap_map _ _

theorem mem_cartan_of_restrictN [(cartan B N).Normal] (hker : π.ker ≤ B ⊓ N) {n : N}
    (hn : restrictN π N n ∈ cartan (B.map π) (N.map π)) : n ∈ cartan B N := by
  rw [cartan_map π (hker.trans inf_le_left), Subgroup.mem_map] at hn
  obtain ⟨m, hm, hmn⟩ := hn
  have h1 : π (m : X) = π (n : X) := by
    have := congrArg (fun z : N.map π => (z : Y)) hmn
    exact this
  have hk : (m : X)⁻¹ * n ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have hmem : (n : X) ∈ B ⊓ N := by
    have h2 : (m : X) * ((m : X)⁻¹ * n) = n := mul_inv_cancel_left _ _
    rw [← h2]
    exact Subgroup.mul_mem _ (by simpa [cartan, Subgroup.mem_subgroupOf] using hm) (hker hk)
  simpa [cartan, Subgroup.mem_subgroupOf] using hmem

end Image

section Weyl

variable {X : Type u} {Y : Type v} [Group X] [Group Y] (π : X →* Y) {B N : Subgroup X}
  [(cartan B N).Normal] [(cartan (B.map π) (N.map π)).Normal]

@[expose] def weylHom (hker : π.ker ≤ B) :
    WeylGroup B N →* WeylGroup (B.map π) (N.map π) :=
  QuotientGroup.map (cartan B N) (cartan (B.map π) (N.map π)) (restrictN π N)
    (cartan_le_comap π hker)

theorem weylHom_mk (hker : π.ker ≤ B) (n : N) :
    weylHom π hker (n : WeylGroup B N) =
      ((restrictN π N n : N.map π) : WeylGroup (B.map π) (N.map π)) := rfl

theorem weylHom_injective (hker : π.ker ≤ B ⊓ N) :
    Function.Injective (weylHom π (hker.trans inf_le_left) :
      WeylGroup B N →* WeylGroup (B.map π) (N.map π)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  induction w using QuotientGroup.induction_on with
  | H n =>
    rw [weylHom_mk, QuotientGroup.eq_one_iff] at hw
    exact (QuotientGroup.eq_one_iff n).2 (mem_cartan_of_restrictN π hker hw)

theorem weylHom_surjective (hker : π.ker ≤ B) :
    Function.Surjective (weylHom π hker :
      WeylGroup B N →* WeylGroup (B.map π) (N.map π)) := by
  intro w'
  induction w' using QuotientGroup.induction_on with
  | H n' =>
    obtain ⟨n, rfl⟩ := restrictN_surjective π n'
    exact ⟨(n : WeylGroup B N), rfl⟩

@[expose] def weylMap (hker : π.ker ≤ B ⊓ N) :
    WeylGroup B N ≃* WeylGroup (B.map π) (N.map π) :=
  MulEquiv.ofBijective (weylHom π (hker.trans inf_le_left))
    ⟨weylHom_injective π hker, weylHom_surjective π (hker.trans inf_le_left)⟩

theorem weylMap_mk (hker : π.ker ≤ B ⊓ N) (n : N) :
    weylMap π hker (n : WeylGroup B N) =
      ((restrictN π N n : N.map π) : WeylGroup (B.map π) (N.map π)) := rfl

theorem mem_dc_map_iff (hker : π.ker ≤ B ⊓ N) (w : WeylGroup B N) (x : X) :
    π x ∈ dc (B.map π) (N.map π) (weylMap π hker w) ↔ x ∈ dc B N w := by
  have hkB : π.ker ≤ B := hker.trans inf_le_left
  rw [mem_dc_iff, mem_dc_iff]
  constructor
  · rintro ⟨n', hn', _, ⟨b₁, hb₁, rfl⟩, _, ⟨b₂, hb₂, rfl⟩, hx⟩
    obtain ⟨n, rfl⟩ := restrictN_surjective π n'
    have hw : (n : WeylGroup B N) = w := by
      apply (weylMap π hker).injective
      rw [← hn', weylMap_mk]
    have hx' : π x = π (b₁ * n * b₂) := by
      rw [hx, map_mul, map_mul, coe_restrictN]
    have hk : (b₁ * n * b₂)⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hx', inv_mul_cancel]
    refine ⟨n, hw, b₁, hb₁, b₂ * ((b₁ * n * b₂)⁻¹ * x), B.mul_mem hb₂ (hkB hk), ?_⟩
    group
  · rintro ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩
    refine ⟨restrictN π N n, ?_, π b₁, ⟨b₁, hb₁, rfl⟩, π b₂, ⟨b₂, hb₂, rfl⟩, ?_⟩
    · rw [← hn, weylMap_mk]
    · rw [map_mul, map_mul, coe_restrictN]

end Weyl

section Tits

variable {X : Type u} {Y : Type v} [Group X] [Group Y] (π : X →* Y) {B N : Subgroup X}
  [(cartan B N).Normal] [(cartan (B.map π) (N.map π)).Normal]

theorem mem_pair_of_weylMap_mem (hker : π.ker ≤ B ⊓ N) {w₁ w₂ w : WeylGroup B N}
    (h : weylMap π hker w ∈ ({weylMap π hker w₁, weylMap π hker w₂} :
      Set (WeylGroup (B.map π) (N.map π)))) : w ∈ ({w₁, w₂} : Set (WeylGroup B N)) := by
  rcases h with h | h
  · exact Or.inl ((weylMap π hker).injective h)
  · exact Or.inr ((weylMap π hker).injective (Set.mem_singleton_iff.1 h))

open Classical in
theorem IsTitsSystem.map (hπ : Function.Surjective π) (hker : π.ker ≤ B ⊓ N)
    {w₁ w₂ : WeylGroup B N} (h : IsTitsSystem B N {w₁, w₂}) :
    IsTitsSystem (B.map π) (N.map π) {weylMap π hker w₁, weylMap π hker w₂} := by
  have hkB : π.ker ≤ B := hker.trans inf_le_left
  have hsub : ∀ {n : N}, ((restrictN π N n : N.map π) : WeylGroup (B.map π) (N.map π)) ∈
      (({weylMap π hker w₁, weylMap π hker w₂} : Finset (WeylGroup (B.map π) (N.map π))) :
        Set _) → (n : WeylGroup B N) ∈ (({w₁, w₂} : Finset (WeylGroup B N)) : Set _) := by
    intro n hn
    rw [← weylMap_mk π hker] at hn
    simp only [Finset.coe_insert, Finset.coe_singleton] at hn ⊢
    exact mem_pair_of_weylMap_mem π hker hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, h.gen, Subgroup.map_top_of_surjective π hπ]
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact (orderOf_injective (weylMap π hker).toMonoidHom (weylMap π hker).injective w₁).trans
        (h.involution _ (by simp))
    · exact (orderOf_injective (weylMap π hker).toMonoidHom (weylMap π hker).injective w₂).trans
        (h.involution _ (by simp))
  · have h1 : Subgroup.closure ((({weylMap π hker w₁, weylMap π hker w₂} :
        Finset (WeylGroup (B.map π) (N.map π))) : Set _)) =
        (Subgroup.closure ((({w₁, w₂} : Finset (WeylGroup B N)) : Set _))).map
          (weylMap π hker).toMonoidHom := by
      rw [MonoidHom.map_closure]
      congr 1
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_pair]
      rfl
    rw [h1, h.closure_eq]
    exact Subgroup.map_top_of_surjective _ (weylMap π hker).surjective
  · intro n' m' hn' y hy
    obtain ⟨n, rfl⟩ := restrictN_surjective π n'
    obtain ⟨m, rfl⟩ := restrictN_surjective π m'
    obtain ⟨_, ⟨_, rfl, _, ⟨b₀, hb₀, rfl⟩, rfl⟩, _, rfl, rfl⟩ := hy
    dsimp only
    have hn : (n : WeylGroup B N) ∈ ({w₁, w₂} : Finset (WeylGroup B N)) := by
      have := hsub (n := n) (by simpa using hn')
      simpa using this
    have hmem : (n : X) * b₀ * (m : X) ∈
        ({(n : X)} : Set X) * (B : Set X) * {(m : X)} :=
      Set.mem_mul.2 ⟨(n : X) * b₀, Set.mem_mul.2 ⟨n, rfl, b₀, hb₀, rfl⟩, m, rfl, rfl⟩
    have hy : π ((n : X) * b₀ * (m : X)) =
        ((restrictN π N n : N.map π) : Y) * π b₀ * ((restrictN π N m : N.map π) : Y) := by
      rw [map_mul, map_mul, coe_restrictN, coe_restrictN]
    rcases h.mul_subset n m hn hmem with h1 | h1
    · left
      rw [← hy, show ((restrictN π N n : N.map π) : WeylGroup (B.map π) (N.map π)) *
          ((restrictN π N m : N.map π) : WeylGroup (B.map π) (N.map π)) =
          weylMap π hker ((n : WeylGroup B N) * (m : WeylGroup B N)) by
        rw [map_mul, weylMap_mk, weylMap_mk]]
      exact (mem_dc_map_iff π hker _ _).2 h1
    · right
      rw [← hy, show ((restrictN π N m : N.map π) : WeylGroup (B.map π) (N.map π)) =
          weylMap π hker (m : WeylGroup B N) from (weylMap_mk π hker m).symm]
      exact (mem_dc_map_iff π hker _ _).2 h1
  · intro n' hn' heq
    obtain ⟨n, rfl⟩ := restrictN_surjective π n'
    have hn : (n : WeylGroup B N) ∈ ({w₁, w₂} : Finset (WeylGroup B N)) := by
      have := hsub (n := n) (by simpa using hn')
      simpa using this
    refine h.ne n hn ?_
    ext x
    constructor
    · rintro ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
      have hx : π ((n : X) * b * (n : X)) ∈ (B.map π : Set Y) := by
        rw [← heq]
        exact Set.mem_mul.2 ⟨((restrictN π N n : N.map π) : Y) * π b,
          Set.mem_mul.2 ⟨_, rfl, π b, ⟨b, hb, rfl⟩, rfl⟩, _, rfl, by
            rw [map_mul, map_mul]; rfl⟩
      obtain ⟨b', hb', hbx⟩ := hx
      have hk : b'⁻¹ * ((n : X) * b * (n : X)) ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hbx, inv_mul_cancel]
      have : (n : X) * b * (n : X) = b' * (b'⁻¹ * ((n : X) * b * (n : X))) := by group
      show (n : X) * b * (n : X) ∈ B
      rw [this]
      exact B.mul_mem hb' (hkB hk)
    · intro hx
      have hx' : π x ∈ (B.map π : Set Y) := ⟨x, hx, rfl⟩
      rw [← heq] at hx'
      obtain ⟨_, ⟨_, rfl, _, ⟨b₀, hb₀, rfl⟩, rfl⟩, _, rfl, hxy⟩ := hx'
      have hxy' : π x = π ((n : X) * b₀ * (n : X)) := by
        rw [map_mul, map_mul]
        exact hxy.symm
      have hk : ((n : X) * b₀ * (n : X))⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxy', inv_mul_cancel]
      have hk' := (MonoidHom.normal_ker π).conj_mem _ hk (n : X)
      have hbB : b₀ * ((n : X) * (((n : X) * b₀ * (n : X))⁻¹ * x) * (n : X)⁻¹) ∈ B :=
        B.mul_mem hb₀ (hkB hk')
      refine Set.mem_mul.2 ⟨(n : X) * (b₀ * ((n : X) * (((n : X) * b₀ * (n : X))⁻¹ * x) *
        (n : X)⁻¹)), Set.mem_mul.2 ⟨_, rfl, _, hbB, rfl⟩, _, rfl, ?_⟩
      group

end Tits

section RootMap

variable {X : Type u} {Y : Type v} [Group X] [Group Y] (π : X →* Y)

theorem image_chainProd (A : ℤ → Subgroup X) (l : List ℤ) :
    π '' chainProd A l = chainProd (fun k => (A k).map π) l := by
  unfold chainProd
  rw [Set.image_list_prod, List.map_map]
  congr 1

theorem list_prod_mem_chainProd (A : ℤ → Subgroup X) (f : ℤ → X) :
    ∀ l : List ℤ, (∀ k ∈ l, f k ∈ A k) → (l.map f).prod ∈ chainProd A l
  | [], _ => by simp [chainProd]
  | k :: l, h => by
    rw [chainProd_cons, List.map_cons, List.prod_cons]
    exact Set.mem_mul.2 ⟨f k, h k (by simp), (l.map f).prod,
      list_prod_mem_chainProd A f l (fun k' hk' => h k' (by simp [hk'])), rfl⟩

theorem conjBy_map (m : X) (A : Subgroup X) :
    conjBy (π m) (A.map π) = (conjBy m A).map π := by
  unfold conjBy
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem ker_le_conj {B : Subgroup X} (hkB : π.ker ≤ B) (g : X) :
    π.ker ≤ B.map (MulAut.conj g).toMonoidHom := by
  intro k hk
  have h1 := (MonoidHom.normal_ker π).conj_mem k hk g⁻¹
  rw [inv_inv] at h1
  exact ⟨g⁻¹ * k * g, hkB h1, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem root_le_U_of_isRootGroupSystem {B N U : Subgroup X} [(cartan B N).Normal]
    {w₁ w₂ : WeylGroup B N} {n : ℕ} {root : ℤ → Subgroup X}
    (h : IsRootGroupSystem B N w₁ w₂ U n root) {k : ℤ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    root k ≤ U := by
  obtain ⟨V, hV, hVU, -, -⟩ := h.subgroup k k hk1 le_rfl hkn
  intro x hx
  have : x ∈ chainProd root (intList k k) :=
    mem_chainProd_of_mem root (mem_intList_iff.2 ⟨le_rfl, le_rfl⟩) hx
  rw [← hV] at this
  exact hVU this

theorem IsRootGroupSystem.map {B N U : Subgroup X} [(cartan B N).Normal]
    [(cartan (B.map π) (N.map π)).Normal] {w₁ w₂ : WeylGroup B N} {n : ℕ}
    {root : ℤ → Subgroup X} (hker : π.ker ≤ B ⊓ N) (hU : U ⊓ π.ker = ⊥)
    (h : IsRootGroupSystem B N w₁ w₂ U n root) :
    IsRootGroupSystem (B.map π) (N.map π) (weylMap π hker w₁) (weylMap π hker w₂) (U.map π) n
      (fun i => (root i).map π) := by
  have hkB : π.ker ≤ B := hker.trans inf_le_left
  have hinf := map_inf_map_of_ker_le π (N := N) hkB
  have hmemU : ∀ f : ℤ → X, (∀ k ∈ intList 1 n, f k ∈ root k) →
      ((intList 1 n).map f).prod ∈ U := by
    intro f hf
    have := list_prod_mem_chainProd root f (intList 1 n) hf
    rw [← h.carrier_eq] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hbot
    apply h.ne_bot i hi
    rw [eq_bot_iff]
    intro x hx
    have hx1 : π x = 1 := by
      have : π x ∈ (root i).map π := ⟨x, hx, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have hxk : x ∈ π.ker := hx1
    have hxB : x ∈ B := hkB hxk
    have hi2 := hi.2
    rcases lt_or_gt_of_ne hi.1 with hneg | hpos
    · have hmem : x ∈ chainProd root ((intList 1 n).map Neg.neg) := by
        refine mem_chainProd_of_mem root (k := i) ?_ hx
        rw [List.mem_map]
        exact ⟨-i, mem_intList_iff.2 ⟨by omega, by omega⟩, by simp⟩
      exact Subgroup.mem_bot.2 (h.meet_one x hxB hmem)
    · have hxU : x ∈ U := root_le_U_of_isRootGroupSystem h (by omega) (by omega) hx
      have : x ∈ U ⊓ π.ker := Subgroup.mem_inf.2 ⟨hxU, hxk⟩
      rw [hU] at this
      exact this
  · intro i hi h' hh' x' hx'
    rw [hinf] at hh'
    obtain ⟨c, hc, rfl⟩ := hh'
    obtain ⟨x, hx, rfl⟩ := hx'
    exact ⟨c * x * c⁻¹, h.invariant i hi c hc x hx, by simp [map_mul, map_inv]⟩
  · rw [Subgroup.coe_map, h.carrier_eq, image_chainProd]
  · intro f g hf hg hfg k hk
    have hf' : ∀ k ∈ intList 1 n, ∃ a ∈ root k, π a = f k := fun k hk => hf k hk
    have hg' : ∀ k ∈ intList 1 n, ∃ a ∈ root k, π a = g k := fun k hk => hg k hk
    choose! f₀ hf₀ hf₀π using hf'
    choose! g₀ hg₀ hg₀π using hg'
    have hπf : π (((intList 1 n).map f₀).prod) = ((intList 1 n).map f).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun k hk => hf₀π k hk
    have hπg : π (((intList 1 n).map g₀).prod) = ((intList 1 n).map g).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun k hk => hg₀π k hk
    have hker1 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπf, hπg, hfg, inv_mul_cancel]
    have hU1 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod ∈ U :=
      U.mul_mem (U.inv_mem (hmemU f₀ hf₀)) (hmemU g₀ hg₀)
    have h0 : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod = 1 := by
      have : (((intList 1 n).map f₀).prod)⁻¹ * ((intList 1 n).map g₀).prod ∈ U ⊓ π.ker :=
        Subgroup.mem_inf.2 ⟨hU1, hker1⟩
      rw [hU] at this
      exact Subgroup.mem_bot.1 this
    have heq : ((intList 1 n).map f₀).prod = ((intList 1 n).map g₀).prod :=
      inv_mul_eq_one.1 h0
    have := h.unique f₀ g₀ hf₀ hg₀ heq k hk
    rw [← hf₀π k hk, ← hg₀π k hk, this]
  · intro i j h1 h2 h3
    rw [← image_chainProd, ← image_chainProd, h.reverse_eq i j h1 h2 h3]
  · intro i j h1 h2 h3
    obtain ⟨V, hV, hVU, hl, hr⟩ := h.subgroup i j h1 h2 h3
    refine ⟨V.map π, ?_, Subgroup.map_mono hVU, ?_, ?_⟩
    · rw [Subgroup.coe_map, hV, image_chainProd]
    · intro hi x' hx' v' hv'
      obtain ⟨x, hx, rfl⟩ := hx'
      obtain ⟨v, hv, rfl⟩ := hv'
      exact ⟨x * v * x⁻¹, hl hi x hx v hv, by simp [map_mul, map_inv]⟩
    · intro hj x' hx' v' hv'
      obtain ⟨x, hx, rfl⟩ := hx'
      obtain ⟨v, hv, rfl⟩ := hv'
      exact ⟨x * v * x⁻¹, hr hj x hx v hv, by simp [map_mul, map_inv]⟩
  · intro m' hm'
    obtain ⟨m, rfl⟩ := restrictN_surjective π m'
    have hm : (m : WeylGroup B N) = w₁ :=
      (weylMap π hker).injective (by rw [weylMap_mk]; exact hm')
    obtain ⟨a1, a2, a3⟩ := h.action₁ m hm
    have e : ((restrictN π N m : N.map π) : Y) = π (m : X) := rfl
    rw [e, conjBy_map, conjBy_map, a1, a2]
    refine ⟨rfl, rfl, fun i hi2 hin => ?_⟩
    obtain ⟨b1, b2⟩ := a3 i hi2 hin
    rw [conjBy_map, conjBy_map, b1, b2]
    exact ⟨rfl, rfl⟩
  · intro m' hm'
    obtain ⟨m, rfl⟩ := restrictN_surjective π m'
    have hm : (m : WeylGroup B N) = w₂ :=
      (weylMap π hker).injective (by rw [weylMap_mk]; exact hm')
    obtain ⟨a1, a2, a3⟩ := h.action₂ m hm
    have e : ((restrictN π N m : N.map π) : Y) = π (m : X) := rfl
    rw [e, conjBy_map, conjBy_map, a1, a2]
    refine ⟨rfl, rfl, fun i hi1 hin => ?_⟩
    obtain ⟨b1, b2⟩ := a3 i hi1 hin
    rw [conjBy_map, conjBy_map, b1, b2]
    exact ⟨rfl, rfl⟩
  · intro x' hx' hx'c
    obtain ⟨b, hb, rfl⟩ := hx'
    have hc : π b ∈ π '' chainProd root ((intList 1 n).map Neg.neg) := by
      rw [image_chainProd]
      exact hx'c
    obtain ⟨c, hcc, hcb⟩ := hc
    have hk : b⁻¹ * c ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcb, inv_mul_cancel]
    have hcB : c ∈ B := by
      have : c = b * (b⁻¹ * c) := by group
      rw [this]
      exact B.mul_mem hb (hkB hk)
    have := h.meet_one c hcB hcc
    rw [← hcb, this, map_one]

theorem IsSplit.map {B N U : Subgroup X} (hker : π.ker ≤ B) (h : IsSplit B N U) :
    IsSplit (B.map π) (N.map π) (U.map π) := by
  obtain ⟨hnil, hBU⟩ := h
  refine ⟨?_, ?_⟩
  · have : Group.IsNilpotent U := hnil
    exact Group.nilpotent_of_surjective (π.subgroupMap U) (π.subgroupMap_surjective U)
  · rw [map_inf_map_of_ker_le π hker]
    simp only [Subgroup.coe_map]
    rw [← Set.image_mul, ← hBU]

theorem IsSaturated.map {B N : Subgroup X} (hπ : Function.Surjective π)
    (hker : π.ker ≤ B ⊓ N) (h : IsSaturated B N) :
    IsSaturated (B.map π) (N.map π) := by
  have hkB : π.ker ≤ B := hker.trans inf_le_left
  unfold IsSaturated
  apply le_antisymm
  · refine le_iInf fun n' => ?_
    obtain ⟨n, rfl⟩ := restrictN_surjective π n'
    rw [map_inf_map_of_ker_le π hkB]
    have e : (B.map π).map (MulAut.conj ((restrictN π N n : N.map π) : Y)⁻¹).toMonoidHom =
        (B.map (MulAut.conj (n : X)⁻¹).toMonoidHom).map π := conjBy_map π (n : X) B
    rw [e]
    exact Subgroup.map_mono ((le_of_eq h).trans (iInf_le _ n))
  · intro y hy
    obtain ⟨x, rfl⟩ := hπ y
    rw [map_inf_map_of_ker_le π hkB]
    have hx : x ∈ B ⊓ N := by
      rw [h]
      refine Subgroup.mem_iInf.2 fun n => ?_
      have h1 := Subgroup.mem_iInf.1 hy (restrictN π N n)
      have e : (B.map π).map (MulAut.conj ((restrictN π N n : N.map π) : Y)⁻¹).toMonoidHom =
          (B.map (MulAut.conj (n : X)⁻¹).toMonoidHom).map π := conjBy_map π (n : X) B
      rw [e] at h1
      obtain ⟨x', hx', hxx⟩ := h1
      have hk : x'⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxx, inv_mul_cancel]
      have hker' := ker_le_conj π hkB ((n : X)⁻¹) hk
      have : x = x' * (x'⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx' hker'
    exact ⟨x, hx, rfl⟩

end RootMap

namespace PreRankTwoSystem

variable {X : Type u} {Y : Type v} [Group X] [Group Y] {n : ℕ}

@[expose] def map (D : PreRankTwoSystem X n) (π : X →* Y) (hπ : Function.Surjective π)
    (hker : π.ker ≤ D.B ⊓ D.N) (hU : D.U ⊓ π.ker = ⊥) : PreRankTwoSystem Y n :=
  have hnorm := cartan_map_normal π (hker.trans inf_le_left) (B := D.B) (N := D.N)
  { B := D.B.map π
    N := D.N.map π
    normal := hnorm
    w₁ := weylMap π hker D.w₁
    w₂ := weylMap π hker D.w₂
    U := D.U.map π
    root := fun i => (D.root i).map π
    isTits := IsTitsSystem.map π hπ hker D.isTits
    w₁_ne_w₂ := fun h => D.w₁_ne_w₂ ((weylMap π hker).injective h)
    isSplit := IsSplit.map π (hker.trans inf_le_left) D.isSplit
    isSaturated := IsSaturated.map π hπ hker D.isSaturated
    card_weyl := by
      rw [← D.card_weyl]
      exact (Nat.card_congr (weylMap π hker).toEquiv).symm
    three_le := D.three_le
    roots := IsRootGroupSystem.map π hker hU D.roots }

end PreRankTwoSystem

end CFSG.GH74.GLS.SP
