module

public import CFSG.GH74.GLS.Balance.Bender.L53Core
public import CFSG.GH74.GLS.Balance.Bender.ExtSylow
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.GH74.GLS.Balance.BenderExt

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime]

@[expose] def ExtCore (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ {Z : Type} [Group Z] (π : Y →* Z), Function.Surjective π → IsPStar p Z →
    ∀ P : Subgroup Y, IsSylowIn p P π.ker → IsPStar p ↥(oResOf p π.ker) →
      oResOf p π.ker ⊔ centralizer (P : Set Y) = ⊤ → oResidual p Y = ⊤ → IsPStar p Y

omit [Fact p.Prime] in
theorem isSylowIn_comap_subtype {Y : Type} [Group Y] {X₀ N P : Subgroup Y}
    (h : IsSylowIn p (P ⊓ X₀) (N ⊓ X₀)) : IsSylowIn p (P.comap X₀.subtype) (N.comap X₀.subtype) := by
  obtain ⟨hle, hpg, hmax⟩ := h
  have hmapP : (P.comap X₀.subtype).map X₀.subtype = P ⊓ X₀ := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hcardP : Nat.card ↥(P.comap X₀.subtype) = Nat.card ↥(P ⊓ X₀) := by
    rw [← hmapP, Subgroup.card_map_of_injective X₀.subtype_injective]
  refine ⟨?_, ?_, fun S hSN hS => ?_⟩
  · intro x hx
    have : X₀.subtype x ∈ N ⊓ X₀ := hle ⟨hx, x.2⟩
    exact this.1
  · have h1 : IsPGroup p ↥((P ⊓ X₀).comap X₀.subtype) := hpg.comap_of_injective X₀.subtype X₀.subtype_injective
    have h2 : (P ⊓ X₀).comap X₀.subtype = P.comap X₀.subtype := by
      ext x; simp
    rwa [h2] at h1
  · have hS' : S.map X₀.subtype ≤ N ⊓ X₀ := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨hSN hs, s.2⟩
    have := hmax _ hS' (hS.map X₀.subtype)
    rw [Subgroup.card_map_of_injective X₀.subtype_injective] at this
    rw [hcardP]; exact this


theorem ext_gamma {Y : Type} [Group Y] [Finite Y]
    (ih : ∀ (Y' : Type) [Group Y'] [Finite Y'], Nat.card Y' < Nat.card Y → ExtCore p Y')
    {Z : Type} [Group Z] (π : Y →* Z) (hπ : Function.Surjective π) (hZ : IsPStar p Z)
    (hY : oResidual p Y = ⊤) (hmin : ∀ M : Subgroup Y, M.Normal → M ≤ π.ker → M = ⊥ ∨ M = π.ker)
    (hZc : Subgroup.center ↥π.ker = ⊥) (hpN : p ∣ Nat.card ↥π.ker) {P : Subgroup Y}
    (hP : IsSylowIn p P π.ker) (h3 : π.ker ⊔ centralizer (P : Set Y) = ⊤) : IsPStar p Y := by
  have hp : p.Prime := Fact.out
  have hNn : π.ker.Normal := inferInstance
  set N := π.ker with hNdef
  set C := centralizer (P : Set Y) with hC
  set X₀ := oResOf p C with hX₀
  have hNX : N ⊔ X₀ = ⊤ := sup_oResOf_eq_top hp hY h3
  have hX₀C : X₀ ≤ C := oResOf_le p C
  have hcommP : ∀ x ∈ X₀, ∀ u ∈ P, u * x = x * u := fun x hx u hu =>
    Subgroup.mem_centralizer_iff.mp (hX₀C hx) u hu
  have hX₀ne : X₀ ≠ ⊤ := by
    intro htop
    have hCtop : C = ⊤ := top_le_iff.mp (htop ▸ hX₀C)
    have hPN : P ≤ N := hP.1
    have hPbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : (⟨u, hPN hu⟩ : ↥N) ∈ Subgroup.center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro n
        apply Subtype.ext
        have : (n : Y) ∈ C := by rw [hCtop]; exact mem_top _
        exact (Subgroup.mem_centralizer_iff.mp this u hu).symm
      rw [hZc, Subgroup.mem_bot] at hu'
      have : u = 1 := congrArg Subtype.val hu'
      rw [this]; exact one_mem _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpN
    have hSN : Subgroup.zpowers (g : Y) ≤ N := Subgroup.zpowers_le.mpr g.2
    have hSc : Nat.card ↥(Subgroup.zpowers (g : Y)) = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    have hSp : IsPGroup p ↥(Subgroup.zpowers (g : Y)) := IsPGroup.of_card (n := 1) (by rw [hSc, pow_one])
    have := hP.2.2 _ hSN hSp
    rw [hSc, hPbot, Subgroup.card_bot] at this
    exact absurd this (by have := hp.two_le; omega)
  have hlt : Nat.card ↥X₀ < Nat.card Y := by
    have hdvd : Nat.card ↥X₀ ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card X₀
    have hne : Nat.card ↥X₀ ≠ Nat.card Y := fun h => hX₀ne (Subgroup.eq_top_of_card_eq X₀ h)
    exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) hne
  have hX₀p : IsPStar p ↥X₀ := by
    refine ih ↥X₀ hlt (π.comp X₀.subtype) ?_ hZ (P.comap X₀.subtype) ?_ ?_ ?_ ?_
    · intro z
      obtain ⟨y, rfl⟩ := hπ z
      have hy : y ∈ N ⊔ X₀ := by rw [hNX]; exact mem_top y
      obtain ⟨n, hn, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      refine ⟨⟨x, hx⟩, ?_⟩
      show π x = π (n * x)
      rw [map_mul, MonoidHom.mem_ker.mp hn, one_mul]
    · rw [← MonoidHom.comap_ker]
      exact isSylowIn_comap_subtype (isSylowIn_inf_of_le_centralizer hP hX₀C)
    · rw [← MonoidHom.comap_ker]
      apply bender_l52i p
      apply coprime_card_oResOf_of_central_sylow (P := P.comap X₀.subtype)
      · exact isSylowIn_comap_subtype (isSylowIn_inf_of_le_centralizer hP hX₀C)
      · intro n _
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact Subtype.ext (hcommP n.1 n.2 u.1 hu)
    · have : centralizer ((P.comap X₀.subtype : Subgroup ↥X₀) : Set ↥X₀) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact Subtype.ext (hcommP x.1 x.2 u.1 hu)
      rw [this, sup_top_eq]
    · exact (oResidual_eq_top_iff X₀).mpr (oResOf_oResOf C)
  rw [isPStar_iff_T]
  refine ⟨hY, fun M hM T hTM hT => ?_⟩
  have hZ' := isPStar_iff_T.mp hZ
  by_cases hMN : M ⊓ N = ⊥
  ·
    have hMn' : (M.map π).Normal := hM.map π hπ
    have h1 := hZ'.2 (M.map π) hMn' (T.map π) (Subgroup.map_mono hTM) (hT.map π)
    rw [eq_top_iff]
    intro y _
    have hy : π y ∈ M.map π ⊔ centralizer ((T.map π : Subgroup Z) : Set Z) := by
      rw [h1]; exact mem_top _
    obtain ⟨a, ha, z, hz, haz⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    obtain ⟨m, hm, rfl⟩ := ha
    have hπc : π (m⁻¹ * y) = z := by
      rw [map_mul, map_inv, ← haz]; group
    have hcT : m⁻¹ * y ∈ centralizer (T : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hmem : (m⁻¹ * y) * t * (m⁻¹ * y)⁻¹ * t⁻¹ ∈ M ⊓ N := by
        refine ⟨?_, ?_⟩
        · exact M.mul_mem (hM.conj_mem t (hTM ht) _) (M.inv_mem (hTM ht))
        · have hk : π ((m⁻¹ * y) * t * (m⁻¹ * y)⁻¹ * t⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπc]
            have := Subgroup.mem_centralizer_iff.mp hz (π t) (Subgroup.mem_map_of_mem π ht)
            rw [← this]; group
          exact hk
      rw [hMN, Subgroup.mem_bot] at hmem
      have h1 := mul_inv_eq_one.mp hmem
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have : y = m * (m⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hm hcT
  ·
    have hNM : N ≤ M := by
      have hnormal : (M ⊓ N).Normal := inferInstance
      rcases hmin (M ⊓ N) hnormal inf_le_right with h | h
      · exact absurd h hMN
      · exact h ▸ inf_le_left
    obtain ⟨R, hR⟩ := exists_isSylowIn p (M ⊓ X₀)
    have hMeq : M = N ⊔ (M ⊓ X₀) := by
      apply le_antisymm
      · intro m hm
        have hm' : m ∈ N ⊔ X₀ := by rw [hNX]; exact mem_top m
        obtain ⟨n, hn, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hm'
        have hx' : x ∈ M := by
          have := M.mul_mem (M.inv_mem (hNM hn)) hm
          simpa using this
        exact Subgroup.mul_mem_sup hn ⟨hx', hx⟩
      · exact sup_le hNM inf_le_left
    have hM₀N : (M ⊓ X₀) ≤ normalizer (N : Set Y) := fun x _ => Subgroup.le_normalizer_of_normal (mem_top x)
    have hRP : R ≤ centralizer (P : Set Y) := fun r hr => hX₀C (hR.1 hr).2
    have hQ : IsSylowIn p (P ⊔ R) M := isSylowIn_sup_of_le_normalizer hMeq hM₀N hP hR hRP
    have hM₀n : ((M ⊓ X₀).subgroupOf X₀).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : Y) ∈ M ⊓ X₀ := hx
      exact ⟨hM.conj_mem _ hx'.1 g, X₀.mul_mem (X₀.mul_mem g.2 hx'.2) (X₀.inv_mem g.2)⟩
    have hkey := isPStar_T_ambient hX₀p inf_le_right hM₀n hR.1 hR.2.1
    have hQtop : M ⊔ centralizer ((P ⊔ R : Subgroup Y) : Set Y) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ N ⊔ X₀ := by rw [hNX]; exact mem_top y
      obtain ⟨n, hn, x, hx, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      have hx2 := hkey hx
      have hX₀norm : (X₀ ⊓ centralizer (R : Set Y)) ≤ normalizer ((M ⊓ X₀ : Subgroup Y) : Set Y) := by
        intro c hc
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · rintro ⟨hwM, hwX⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer_of_normal (mem_top c)) w).mp hwM,
            by
              have := X₀.mul_mem (X₀.mul_mem hc.1 hwX) (X₀.inv_mem hc.1)
              exact this⟩
        · rintro ⟨hwM, hwX⟩
          refine ⟨?_, ?_⟩
          · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer_of_normal (mem_top c)) w).mpr hwM
            exact this
          · have h1 := X₀.mul_mem (X₀.mul_mem (X₀.inv_mem hc.1) hwX) hc.1
            simpa [mul_assoc] using h1
      obtain ⟨a, ha, c, hc, hac⟩ := (mem_sup_of_le_normalizer hX₀norm).mp hx2
      have hcP : c ∈ centralizer ((P ⊔ R : Subgroup Y) : Set Y) := by
        have h1 : P ⊔ R ≤ centralizer ({c} : Set Y) := by
          refine sup_le (fun u hu => ?_) (fun r hr => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact hcommP c hc.1 u hu
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.mp hc.2 r hr
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hh)
      have : n * x = (n * a) * c := by rw [mul_assoc, hac]
      rw [this]
      exact Subgroup.mul_mem_sup (M.mul_mem (hNM hn) ha.1) hcP
    exact sup_centralizer_eq_top_of_sylow hQ hQtop hTM hT


omit [Fact p.Prime] in
theorem isPGroup_of_oResOf_eq_bot {Y : Type} [Group Y] [Finite Y] (hp : p.Prime) {N : Subgroup Y}
    (h : oResOf p N = ⊥) : IsPGroup p ↥N := by
  intro x
  obtain ⟨e, he⟩ := exists_pow_mem_oResOf hp x.2
  rw [h, Subgroup.mem_bot] at he
  exact ⟨e, Subtype.ext he⟩

omit [Fact p.Prime] in
theorem oResOf_eq_bot_of_isPGroup {Y : Type} [Group Y] {N : Subgroup Y} (h : IsPGroup p ↥N) :
    oResOf p N = ⊥ := by
  refine le_bot_iff.mp (oResOf_le_of fun x hx hcop => ?_)
  obtain ⟨k, hk⟩ := h ⟨x, hx⟩
  have hxk : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h1 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp h1

theorem ext_pgroupN {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) (hZ : IsPStar p Z) (hY : oResidual p Y = ⊤)
    (hN : IsPGroup p ↥π.ker) {P : Subgroup Y} (hP : IsSylowIn p P π.ker)
    (hC : centralizer (P : Set Y) = ⊤) : IsPStar p Y := by
  have hPeq : P = π.ker := Subgroup.eq_of_le_of_card_ge hP.1 (hP.2.2 _ le_rfl hN)
  refine ext_central π hπ hZ hY hN fun n hn => ?_
  rw [Subgroup.mem_center_iff]
  intro g
  have hnP : n ∈ P := hPeq ▸ hn
  have : g ∈ centralizer (P : Set Y) := by rw [hC]; exact mem_top g
  exact (Subgroup.mem_centralizer_iff.mp this n hnP).symm

theorem ext_minimal {Y : Type} [Group Y] [Finite Y]
    (ih : ∀ (Y' : Type) [Group Y'] [Finite Y'], Nat.card Y' < Nat.card Y → ExtCore p Y')
    {Z : Type} [Group Z] (π : Y →* Z) (hπ : Function.Surjective π) (hZ : IsPStar p Z)
    (hY : oResidual p Y = ⊤) (N : Subgroup Y) (hNk : π.ker = N) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup Y, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    {P : Subgroup Y} (hP : IsSylowIn p P N) (h3 : N ⊔ centralizer (P : Set Y) = ⊤) : IsPStar p Y := by
  subst hNk
  have hNn : π.ker.Normal := inferInstance
  rcases minimal_normal_trichotomy (p := p) hN1 hmin with ⟨hpg, hab⟩ | hcop | ⟨hZc, hpN, -⟩
  · have hPeq : P = π.ker := Subgroup.eq_of_le_of_card_ge hP.1 (hP.2.2 _ le_rfl hpg)
    have hC : centralizer (P : Set Y) = ⊤ := by
      have hle : π.ker ≤ centralizer (P : Set Y) := hPeq ▸ hab
      rw [← h3, sup_eq_right.mpr hle]
    exact ext_pgroupN π hπ hZ hY hpg hP hC
  · exact ext_primeN π hπ hZ hY hcop
  · exact ext_gamma ih π hπ hZ hY hmin hZc hpN hP h3


theorem extCore_all : ∀ (n : ℕ) (Y : Type) [Group Y] [Finite Y], Nat.card Y = n → ExtCore p Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y _ _ hn Z _ π hπ hZ P hP hL h3 hY
  have hp : p.Prime := Fact.out
  have ih' : ∀ (Y' : Type) [Group Y'] [Finite Y'], Nat.card Y' < Nat.card Y → ExtCore p Y' :=
    fun Y' _ _ hlt => ih _ (hn ▸ hlt) Y' rfl
  have hNn : π.ker.Normal := inferInstance
  set N := π.ker with hNdef
  by_cases hpg : IsPGroup p ↥N
  · have hL0 : oResOf p N = ⊥ := oResOf_eq_bot_of_isPGroup hpg
    have hC : centralizer (P : Set Y) = ⊤ := by rw [hL0, bot_sup_eq] at h3; exact h3
    exact ext_pgroupN π hπ hZ hY hpg hP hC
  by_cases hpd : p ∣ Nat.card ↥N
  swap
  · exact ext_primeN π hπ hZ hY hpd
  have hL1 : oResOf p N ≠ ⊥ := fun h => hpg (isPGroup_of_oResOf_eq_bot hp h)
  have hLn : (oResOf p N).Normal :=
    ⟨fun x hx g => conj_mem_oResOf (Subgroup.le_normalizer_of_normal (mem_top g)) hx⟩
  obtain ⟨N₁, hN₁n, hN₁L, hN₁1, hN₁min⟩ := CFSG.exists_minimal_normal_le (oResOf p N) hLn hL1
  have hN₁N : N₁ ≤ N := hN₁L.trans (oResOf_le p N)
  have hmin₁ : ∀ M : Subgroup Y, M.Normal → M ≤ N₁ → M = ⊥ ∨ M = N₁ := by
    intro M hM hMN
    by_cases h : M = ⊥
    · exact Or.inl h
    · exact Or.inr (hN₁min M hM hMN h)
  set ρ := QuotientGroup.mk' N₁ with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective N₁
  have hlt₁ : Nat.card (Y ⧸ N₁) < Nat.card Y := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N₁
    have h2 : 1 < Nat.card ↥N₁ := (Subgroup.one_lt_card_iff_ne_bot N₁).mpr hN₁1
    have h4 : 0 < Nat.card (Y ⧸ N₁) := Nat.card_pos
    rw [h1]
    exact lt_mul_of_one_lt_right h4 h2
  have hker₁ : N₁ ≤ π.ker := hN₁N
  set π₁ := QuotientGroup.lift N₁ π hker₁ with hπ₁
  have hπ₁s : Function.Surjective π₁ := by
    intro z
    obtain ⟨y, rfl⟩ := hπ z
    exact ⟨(y : Y ⧸ N₁), rfl⟩
  have hkerπ₁ : π₁.ker = N.map ρ := QuotientGroup.ker_lift N₁ π hker₁
  have hP₁ : IsSylowIn p (P.map ρ) π₁.ker := by
    rw [hkerπ₁]; exact isSylowIn_map_surjective ρ hρs hP
  have hL₁ : IsPStar p ↥(oResOf p π₁.ker) := by
    rw [hkerπ₁, ← map_oResOf hp ρ N]
    exact IsPStar.of_surjective (ρ.subgroupMap (oResOf p N)) (ρ.subgroupMap_surjective _) hL
  have h3₁ : oResOf p π₁.ker ⊔ centralizer ((P.map ρ : Subgroup (Y ⧸ N₁)) : Set (Y ⧸ N₁)) = ⊤ := by
    rw [hkerπ₁, ← map_oResOf hp ρ N, eq_top_iff]
    have h1 : (oResOf p N ⊔ centralizer (P : Set Y)).map ρ = ⊤ := by
      rw [h3]; exact Subgroup.map_top_of_surjective ρ hρs
    rw [Subgroup.map_sup] at h1
    rw [← h1]
    refine sup_le_sup_left ?_ _
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc u hu]
  have hY₁ : oResidual p (Y ⧸ N₁) = ⊤ := by
    rw [← map_oResidual hp ρ hρs, hY]; exact Subgroup.map_top_of_surjective ρ hρs
  have hZ₁ : IsPStar p (Y ⧸ N₁) := ih' (Y ⧸ N₁) hlt₁ π₁ hπ₁s hZ _ hP₁ hL₁ h3₁ hY₁
  have hρker : ρ.ker = N₁ := QuotientGroup.ker_mk' N₁
  have hP₁' : IsSylowIn p (P ⊓ N₁) N₁ := by
    have hS : CFSG.ABGLocalTools.IsSylowOf p P N := isSylowIn_iff_isSylowOf.mp hP
    exact isSylowIn_iff_isSylowOf.mpr
      (hS.inf_of_le_normalizer hN₁N (Subgroup.le_normalizer_of_normal))
  have h3' : N₁ ⊔ centralizer ((P ⊓ N₁ : Subgroup Y) : Set Y) = ⊤ := by
    have hN₁L' : (N₁.subgroupOf (oResOf p N)).Normal := hN₁n.comap _
    have hTp : IsPGroup p ↥(P ⊓ N₁) := hP.2.1.to_le inf_le_left
    have hkey := isPStar_T_ambient hL hN₁L hN₁L' inf_le_right hTp
    rw [eq_top_iff, ← h3]
    refine sup_le (hkey.trans (sup_le le_sup_left (inf_le_right.trans le_sup_right))) ?_
    exact (Subgroup.centralizer_le (by exact SetLike.coe_subset_coe.mpr inf_le_left)).trans le_sup_right
  exact ext_minimal ih' ρ hρs hZ₁ hY N₁ hρker hN₁1 hmin₁ hP₁' h3'


omit [Fact p.Prime] in
theorem oResOf_inf_eq {G : Type} [Group G] {N X' : Subgroup G} (h : oResOf p N ≤ X') :
    oResOf p (N ⊓ X') = oResOf p N := by
  apply le_antisymm (oResOf_mono inf_le_left)
  exact oResOf_le_of fun x hx hcop => mem_oResOf ⟨hx, h (mem_oResOf hx hcop)⟩ hcop

omit [Fact p.Prime] in
theorem mem_normalizer_oResOf {G : Type} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer (oResOf p X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_oResOf hg, fun h => ?_⟩
  have := conj_mem_oResOf (Subgroup.inv_mem _ hg) h
  simpa [mul_assoc] using this

omit [Fact p.Prime] in
theorem mem_normalizer_inf' {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro w
  exact and_congr (hA w) (hB w)

end CFSG.GH74.GLS.Balance.BenderExt

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance.BenderExt
open scoped commutatorElement

theorem bender_l53_uncond (p : ℕ) [Fact p.Prime] : BenderL53 p := by
  intro G _ _ X N P _ hNX hP hZ hL h3
  have hp : p.Prime := Fact.out
  set X' := oResOf p X with hX'
  have hX'X : X' ≤ X := oResOf_le p X
  have hLX' : oResOf p N ≤ X' := oResOf_mono hNX
  have hXN : X ≤ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX
  have hXX' : X ≤ normalizer (X' : Set G) := fun g hg => mem_normalizer_oResOf (Subgroup.le_normalizer hg)
  have hXL : X ≤ normalizer (oResOf p N : Set G) := fun g hg => mem_normalizer_oResOf (hXN hg)
  set Nx := N.subgroupOf X with hNx
  set π₀ : ↥X' →* ↥X ⧸ Nx := (QuotientGroup.mk' Nx).comp (Subgroup.inclusion hX'X) with hπ₀
  have hπ₀s : Function.Surjective π₀ := by
    intro z
    have hz : z ∈ oResidual p (↥X ⧸ Nx) := by rw [hZ.1]; exact mem_top z
    rw [← map_oResidual hp (QuotientGroup.mk' Nx) (QuotientGroup.mk'_surjective Nx)] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwX' : (w : G) ∈ X' := ⟨w, hw, rfl⟩
    exact ⟨⟨(w : G), hwX'⟩, rfl⟩
  have hker : π₀.ker = N.comap X'.subtype := by
    ext y
    rw [MonoidHom.mem_ker, hπ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hNnorm : N ≤ normalizer ((N ⊓ X' : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_inf' (Subgroup.le_normalizer hn) (hXX' (hNX hn))
  have hS : CFSG.ABGLocalTools.IsSylowOf p P N := isSylowIn_iff_isSylowOf.mp hP
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ (N ⊓ X')) (N ⊓ X') :=
    hS.inf_of_le_normalizer inf_le_left hNnorm
  have hPeq : P ⊓ (N ⊓ X') = P ⊓ X' := by
    ext x
    exact ⟨fun ⟨hP', _, hX⟩ => ⟨hP', hX⟩, fun ⟨hP', hX⟩ => ⟨hP', hP.1 hP', hX⟩⟩
  rw [hPeq] at hS'
  have hS'' : IsSylowIn p (P ⊓ X') (N ⊓ X') := isSylowIn_iff_isSylowOf.mpr hS'
  have hP'' : IsSylowIn p (P.comap X'.subtype) (N.comap X'.subtype) := isSylowIn_comap_subtype hS''
  have hN₀eq : (oResOf p (N.comap X'.subtype)).map X'.subtype = oResOf p N := by
    rw [map_oResOf hp, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm, oResOf_inf_eq hLX']
  have hN₀p : IsPStar p ↥(oResOf p (N.comap X'.subtype)) := by
    have e : ↥(oResOf p (N.comap X'.subtype)) ≃* ↥(oResOf p N) :=
      (Subgroup.equivMapOfInjective _ X'.subtype X'.subtype_injective).trans
        (MulEquiv.subgroupCongr hN₀eq)
    exact IsPStar.of_mulEquiv e.symm hL
  have h3'' : oResOf p (N.comap X'.subtype) ⊔
      centralizer ((P.comap X'.subtype : Subgroup ↥X') : Set ↥X') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : G) ∈ oResOf p N ⊔ (X ⊓ centralizer (P : Set G)) := h3 y.2
    have hnorm : (X ⊓ centralizer (P : Set G)) ≤ normalizer ((oResOf p N : Subgroup G) : Set G) :=
      inf_le_left.trans hXL
    obtain ⟨o, ho, d, hd, hod⟩ := (mem_sup_of_le_normalizer hnorm).mp hy
    have hoX' : o ∈ X' := hLX' ho
    have hdX' : d ∈ X' := by
      have : d = o⁻¹ * (y : G) := by rw [← hod]; group
      rw [this]; exact X'.mul_mem (X'.inv_mem hoX') y.2
    have ho' : (⟨o, hoX'⟩ : ↥X') ∈ oResOf p (N.comap X'.subtype) := by
      have : o ∈ (oResOf p (N.comap X'.subtype)).map X'.subtype := by rw [hN₀eq]; exact ho
      obtain ⟨w, hw, hwo⟩ := this
      have : w = ⟨o, hoX'⟩ := Subtype.ext hwo
      rwa [← this]
    have hd' : (⟨d, hdX'⟩ : ↥X') ∈ centralizer ((P.comap X'.subtype : Subgroup ↥X') : Set ↥X') := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hd.2 u hu)
    have hyeq : y = ⟨o, hoX'⟩ * ⟨d, hdX'⟩ := Subtype.ext hod.symm
    rw [hyeq]
    exact Subgroup.mul_mem_sup ho' hd'
  refine extCore_all (Nat.card ↥X') ↥X' rfl π₀ hπ₀s hZ (P.comap X'.subtype) ?_ ?_ ?_ ?_
  · rw [hker]; exact hP''
  · rw [hker]; exact hN₀p
  · rw [hker]; exact h3''
  · exact (oResidual_eq_top_iff X').mpr (oResOf_oResOf X)

theorem bender_l53 {p : ℕ} [Fact p.Prime] (_h52i : BenderL52i p) (_h52ii : BenderL52ii p)
    (_h52iii : BenderL52iii p) (_hq42 : BenderQ42iii p) : BenderL53 p :=
  bender_l53_uncond p

end CFSG.GH74.GLS.Balance
