module

public import CFSG.GH74.Uniqueness.ZStarSylow
import CFSG.GroupTheory.ThompsonAxB

public section

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.Uniqueness

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

section Perfect

variable {G : Type} [Group G]

theorem le_sup_centralizer_of_outer_solvable {I Z : Subgroup G} (hZ : Group.IsPerfect ↥Z)
    (hZN : Z ≤ Subgroup.normalizer (I : Set G)) (hOut : Group.IsSolvable (Outer ↥I)) :
    Z ≤ I ⊔ Subgroup.centralizer (I : Set G) := by
  classical
  let ψ : ↥Z →* Outer ↥I :=
    (QuotientGroup.mk' (inner ↥I)).comp ((I.normalizerMonoidHom).comp (Subgroup.inclusion hZN))
  have hperf : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hsolv : Group.IsSolvable ↥ψ.range := inferInstance
  have htriv : ∀ z : ↥Z, ψ z = 1 := by
    intro z
    by_contra hz
    have : Nontrivial ↥ψ.range :=
      ⟨⟨⟨ψ z, z, rfl⟩, 1, fun h => hz (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) hsolv
  intro z hz
  have h1 : ψ ⟨z, hz⟩ = 1 := htriv ⟨z, hz⟩
  have h2 : (I.normalizerMonoidHom ⟨z, hZN hz⟩) ∈ inner ↥I := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨i, hi⟩ := h2
  have hconj : ∀ x ∈ I, (i : G) * x * (i : G)⁻¹ = z * x * z⁻¹ := by
    intro x hx
    have := congrArg (fun a : MulAut ↥I => ((a ⟨x, hx⟩ : ↥I) : G)) hi
    simpa using this
  have hc : (i : G)⁻¹ * z ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hconj x hx
    calc x * ((i : G)⁻¹ * z) = (i : G)⁻¹ * ((i : G) * x * (i : G)⁻¹) * z := by group
      _ = (i : G)⁻¹ * (z * x * z⁻¹) * z := by rw [this]
      _ = (i : G)⁻¹ * z * x := by group
  have hz' : z = (i : G) * ((i : G)⁻¹ * z) := by group
  rw [hz']
  exact Subgroup.mul_mem_sup i.2 hc

end Perfect

section PerfectLe

variable {X : Type} [Group X]

theorem perfect_le_of_outer_solvable {O K Y : Subgroup X} [O.Normal] [K.Normal]
    (hY : Group.IsPerfect ↥Y)
    (hOut : Group.IsSolvable (Outer ↥(K.map (QuotientGroup.mk' O))))
    (hC : Group.IsSolvable ↥((Subgroup.centralizer
      ((K.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O))).comap (QuotientGroup.mk' O))) :
    Y ≤ K := by
  classical
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  set Kb : Subgroup (X ⧸ O) := K.map π with hKb
  set Ct : Subgroup X := (Subgroup.centralizer (Kb : Set (X ⧸ O))).comap π with hCt
  have hKbn : Kb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective O)
  have hperf : Group.IsPerfect ↥(Y.map π) := Group.IsPerfect.map π
  have hYb : Y.map π ≤ Subgroup.normalizer (Kb : Set (X ⧸ O)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hKbn]; exact le_top
  have hle := le_sup_centralizer_of_outer_solvable hperf hYb hOut
  have hOCt : O ≤ Ct := by
    intro o ho
    show π o ∈ Subgroup.centralizer (Kb : Set (X ⧸ O))
    have : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    rw [this]; exact Subgroup.one_mem _
  have hYK : ∀ y ∈ Y, ∃ k ∈ K, ∃ c ∈ Ct, y = k * c := by
    intro y hy
    have hmem : π y ∈ Kb ⊔ Subgroup.centralizer (Kb : Set (X ⧸ O)) := hle (Subgroup.mem_map_of_mem π hy)
    have hmem' : π y ∈ ((Kb ⊔ Subgroup.centralizer (Kb : Set (X ⧸ O)) : Subgroup (X ⧸ O)) : Set (X ⧸ O)) := hmem
    rw [Subgroup.normal_mul] at hmem'
    obtain ⟨kb, hkb, cb, hcb, hkc⟩ := hmem'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hkb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
    have hcC : c ∈ Ct := hcb
    have hyo : (k * c)⁻¹ * y ∈ O := by
      rw [← QuotientGroup.eq]
      have : π (k * c) = π y := by rw [map_mul]; exact hkc
      exact this
    obtain ⟨o, ho⟩ : ∃ o ∈ O, y = k * c * o := ⟨(k * c)⁻¹ * y, hyo, by group⟩
    refine ⟨k, hk, c * o, Ct.mul_mem hcC (hOCt ho.1), ?_⟩
    rw [ho.2]; group
  set σ : X →* X ⧸ K := QuotientGroup.mk' K with hσ
  have hperf2 : Group.IsPerfect ↥(Y.map σ) := Group.IsPerfect.map σ
  have hsolvCt : Group.IsSolvable ↥(Ct.map σ) :=
    Group.isSolvable_of_surjective (f := σ.subgroupMap Ct) (σ.subgroupMap_surjective Ct)
  have hle2 : Y.map σ ≤ Ct.map σ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk, c, hc, rfl⟩ := hYK y hy
    refine ⟨c, hc, ?_⟩
    show σ c = σ (k * c)
    have hσk : σ k = 1 := (QuotientGroup.eq_one_iff k).2 hk
    rw [map_mul, hσk, one_mul]
  have hsolvY : Group.IsSolvable ↥(Y.map σ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle2)
  have htriv : Y.map σ = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(Y.map σ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable (G := ↥(Y.map σ)) hsolvY
  intro y hy
  have : σ y ∈ Y.map σ := Subgroup.mem_map_of_mem σ hy
  rw [htriv, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff y).1 this

end PerfectLe

section SylowConj

variable {X : Type} [Group X] [Finite X]

theorem isSylowOf_conjugate_of_mem_normalizer {p : ℕ} [Fact p.Prime] {S H : Subgroup X}
    (hS : ABGLocalTools.IsSylowOf p S H) {c : X} (hc : c ∈ normalizer (H : Set X)) :
    ABGLocalTools.IsSylowOf p (conjugate S c) H := by
  have hcH : conjugate H c = H := conjugate_eq_iff_mem_normalizer.mpr hc
  have hle : conjugate S c ≤ H := by
    rw [← hcH]
    intro x hx
    rw [mem_conjugate_iff] at hx ⊢
    exact hS.le hx
  apply ABGLocalTools.isSylowOf_of_card hle
  have hcard : Nat.card ↥(conjugate S c) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  rw [hcard]
  exact hS.card_eq

theorem exists_mul_mem_normalizer {p : ℕ} [Fact p.Prime] {O R : Subgroup X} [O.Normal]
    (hR : ABGLocalTools.IsSylowOf p R O) (k : X) : ∃ w ∈ O, k * w⁻¹ ∈ normalizer (R : Set X) := by
  have hk : k ∈ normalizer (O : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top k
  obtain ⟨w, hw, hwR⟩ := exists_conj_of_isSylowOf hR (isSylowOf_conjugate_of_mem_normalizer hR hk)
  refine ⟨w, hw, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : (w⁻¹ * x * w) ∈ conjugate R w ↔ w * (w⁻¹ * x * w) * w⁻¹ ∈ R := mem_conjugate_iff
  have h2 : (w⁻¹ * x * w) ∈ conjugate R k ↔ k * (w⁻¹ * x * w) * k⁻¹ ∈ R := mem_conjugate_iff
  rw [hwR] at h1
  have e1 : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
  have e2 : k * (w⁻¹ * x * w) * k⁻¹ = k * w⁻¹ * x * (k * w⁻¹)⁻¹ := by group
  rw [e1] at h1
  rw [e2] at h2
  exact h1.symm.trans h2 |>.symm.symm

end SylowConj


section Core

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isZStarIn_sup_zpowers {O : Subgroup X} [O.Normal] (hO : Odd (Nat.card O)) (u : X) :
    IsZStarIn (O ⊔ zpowers u) u := by
  refine ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers u), O, le_sup_left, inferInstance, hO, ?_⟩
  intro m hm
  have hm' : m ∈ ((O ⊔ zpowers u : Subgroup X) : Set X) := hm
  rw [Subgroup.normal_mul] at hm'
  obtain ⟨o, ho, h, hh, rfl⟩ := hm'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have hcomm : u ^ j * u = u * u ^ j := (Commute.self_zpow u j).eq.symm
  have e : o * u ^ j * u * (o * u ^ j)⁻¹ * u⁻¹ = o * (u * o⁻¹ * u⁻¹) := by
    calc o * u ^ j * u * (o * u ^ j)⁻¹ * u⁻¹ = o * (u ^ j * u) * (u ^ j)⁻¹ * o⁻¹ * u⁻¹ := by group
      _ = o * (u * u ^ j) * (u ^ j)⁻¹ * o⁻¹ * u⁻¹ := by rw [hcomm]
      _ = o * (u * o⁻¹ * u⁻¹) := by group
  rw [e]
  exact O.mul_mem ho (Subgroup.Normal.conj_mem inferInstance _ (O.inv_mem ho) u)

end Core

section MainCore

variable {X : Type} [Group X] [Finite X]

theorem core_false {O K Mx Q I : Subgroup X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [hOn : O.Normal] (hOodd : Odd (Nat.card O)) [hKn : K.Normal]
    (hKs : IsSimpleGroup ↥(K.map (QuotientGroup.mk' O)))
    (hOut : Group.IsSolvable (Outer ↥(K.map (QuotientGroup.mk' O))))
    (hCsolv : Group.IsSolvable ↥((Subgroup.centralizer
      ((K.map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) : Set (X ⧸ O))).comap (QuotientGroup.mk' O)))
    (hQp : IsPGroup p ↥Q) (hQO : Q ≤ O)
    (hCQ : ∀ x : X, (∀ q ∈ Q, x * q = q * x) → x ∈ Mx)
    (hIperf : Group.IsPerfect ↥I)
    (hIodd : ∀ N : Subgroup X, N ≤ I → (N.subgroupOf I).Normal → Odd (Nat.card N) → N = ⊥)
    (hIns : ¬ Group.IsSolvable ↥I) (hIQ : ∀ i ∈ I, ∀ q ∈ Q, i * q = q * i)
    (hIMn : ∀ m ∈ Mx, ∀ i ∈ I, m * i * m⁻¹ ∈ I)
    (hsec : ∀ D : Subgroup X, D ≤ Mx → ∀ f : ↥D →* ↥(K.map (QuotientGroup.mk' O)),
      ¬ Function.Surjective f) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  set Kb : Subgroup (X ⧸ O) := K.map π with hKb
  have hIK : I ≤ K := perfect_le_of_outer_solvable hIperf hOut hCsolv
  have hIev : Even (Nat.card ↥I) := by
    by_contra hodd
    exact hIns (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.1 hodd))
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥I) 2 (even_iff_two_dvd.1 hIev)
  set u : X := (u₀ : X) with hu
  have huI : u ∈ I := u₀.2
  have hu2 : orderOf u = 2 := by rw [hu, Subgroup.orderOf_coe]; exact hu₀

  have huO : u ∈ normalizer (O : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]; exact Subgroup.mem_top u
  have huQ : u ∈ normalizer (Q : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hIQ u huI h hh
      rw [show u * h * u⁻¹ = h by rw [this]; group]
      exact hh
    · intro hh
      have hc : ∀ q ∈ Q, u⁻¹ * q = q * u⁻¹ := fun q hq => by
        have := hIQ u huI q hq
        calc u⁻¹ * q = u⁻¹ * (q * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * q) * u⁻¹ := by rw [this]
          _ = q * u⁻¹ := by group
      have : u⁻¹ * (u * h * u⁻¹) * u = h := by group
      rw [← this]
      have h2 : u⁻¹ * (u * h * u⁻¹) = (u * h * u⁻¹) * u⁻¹ := hc _ hh
      rw [h2]
      have h3 : u * h * u⁻¹ * u⁻¹ * u = u * h * u⁻¹ := by group
      rw [h3]; exact hh
  obtain ⟨R, hR, hQR, huR⟩ := CFSG.GH74.Uniqueness.exists_invariant_sylow (W := O) (P := Q) (t := u) hp hp2 hu2 huO
    (isZStarIn_sup_zpowers hOodd u) hQO hQp huQ

  have hOKO : O ≤ K ⊔ O := le_sup_right
  have hKKO : K ≤ K ⊔ O := le_sup_left
  set Ch : Subgroup X := Subgroup.centralizer (R : Set X) ⊓ (K ⊔ O) with hCh
  have hcover : ∀ k ∈ K ⊔ O, ∃ n ∈ normalizer (R : Set X) ⊓ (K ⊔ O), π n = π k := by
    intro k hk
    obtain ⟨w, hw, hn⟩ := exists_mul_mem_normalizer hR k
    refine ⟨k * w⁻¹, ⟨hn, (K ⊔ O).mul_mem hk ((K ⊔ O).inv_mem (hOKO hw))⟩, ?_⟩
    have : π w = 1 := (QuotientGroup.eq_one_iff w).2 hw
    rw [map_mul, map_inv, this]; simp
  have hChn : ∀ n ∈ normalizer (R : Set X) ⊓ (K ⊔ O), ∀ c ∈ Ch, n * c * n⁻¹ ∈ Ch := by
    intro n hn c hc
    have hn1 : n ∈ normalizer (R : Set X) := (Subgroup.mem_inf.1 hn).1
    have hn2 : n ∈ K ⊔ O := (Subgroup.mem_inf.1 hn).2
    have hc1 : c ∈ Subgroup.centralizer (R : Set X) := (Subgroup.mem_inf.1 hc).1
    have hc2 : c ∈ K ⊔ O := (Subgroup.mem_inf.1 hc).2
    refine Subgroup.mem_inf.2 ⟨?_, (K ⊔ O).mul_mem ((K ⊔ O).mul_mem hn2 hc2) ((K ⊔ O).inv_mem hn2)⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 : n⁻¹ * r * n ∈ R := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (R : Set X)).inv_mem hn1)) r
      have e : n⁻¹ * r * n⁻¹⁻¹ = n⁻¹ * r * n := by group
      rw [e] at this
      exact this.1 hr
    have h2 := Subgroup.mem_centralizer_iff.1 hc1 _ h1
    calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [h2]
      _ = n * c * n⁻¹ * r := by group
  have hCKO : ∀ c ∈ Ch, π c ∈ Kb := by
    intro c hc
    have hc2 : c ∈ ((K ⊔ O : Subgroup X) : Set X) := (Subgroup.mem_inf.1 hc).2
    rw [Subgroup.normal_mul] at hc2
    obtain ⟨k, hk, o, ho, rfl⟩ := hc2
    have : π o = 1 := (QuotientGroup.eq_one_iff o).2 ho
    rw [map_mul, this, mul_one]
    exact Subgroup.mem_map_of_mem π hk
  have hΘn : ((Ch.map π).subgroupOf Kb).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, hcn⟩ := hn
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨m, hm, hmk⟩ := hcover k (hKKO hk)
    refine ⟨m * c * m⁻¹, hChn m hm c hc, ?_⟩
    have : ((g * n * g⁻¹ : ↥Kb) : X ⧸ O) = (g : X ⧸ O) * (n : X ⧸ O) * (g : X ⧸ O)⁻¹ := rfl
    rw [this, ← hkg, ← hcn, map_mul, map_mul, map_inv, hmk]
  have hChMx : ∀ c ∈ Ch, c ∈ Mx := fun c hc => hCQ c (fun q hq =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1 q (hQR hq)).symm)
  have hChO : Ch ≤ O := by
    have := hΘn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Ch.map π).subgroupOf Kb) with hbot | htop
    · intro c hc
      have h1 : (⟨π c, hCKO c hc⟩ : ↥Kb) ∈ (Ch.map π).subgroupOf Kb :=
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem π hc)
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff c).1 (congrArg Subtype.val h1)
    · exfalso
      let f : ↥Ch →* ↥Kb :=
        { toFun := fun c => ⟨π c, hCKO c c.2⟩
          map_one' := by apply Subtype.ext; simp
          map_mul' := fun a b => by apply Subtype.ext; simp }
      have hf : Function.Surjective f := by
        intro kb
        have h1 : kb ∈ (Ch.map π).subgroupOf Kb := by rw [htop]; exact Subgroup.mem_top kb
        obtain ⟨c, hc, hck⟩ := Subgroup.mem_subgroupOf.1 h1
        exact ⟨⟨c, hc⟩, Subtype.ext hck⟩
      exact hsec Ch hChMx f hf

  have hnc : ∃ r ∈ R, u * r ≠ r * u := by
    by_contra h
    have h' : ∀ r ∈ R, u * r = r * u := fun r hr => by
      by_contra hne
      exact h ⟨r, hr, hne⟩
    have huCh : u ∈ Ch := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 (fun r hr => (h' r hr).symm),
      hKKO.trans le_rfl (hIK huI)⟩
    have huO' : u ∈ O := hChO huCh
    have h1 : orderOf (⟨u, huO'⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hu2] at h1
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h1)

  have hRp : IsPGroup p ↥R := hR.isPGroup
  have hZuN : zpowers u ≤ normalizer (R : Set X) := Subgroup.zpowers_le.2 huR
  have hQN : Q ≤ normalizer (R : Set X) := hQR.trans Subgroup.le_normalizer
  let α : ↥(zpowers u) →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hZuN)
  let β : ↥Q →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hQN)
  have hαapp : ∀ (a : ↥(zpowers u)) (r : ↥R), ((α a r : ↥R) : X) = (a : X) * (r : X) * (a : X)⁻¹ := by
    intro a r
    rfl
  have hβapp : ∀ (b : ↥Q) (r : ↥R), ((β b r : ↥R) : X) = (b : X) * (r : X) * (b : X)⁻¹ := by
    intro b r
    rfl
  have hzI : zpowers u ≤ I := Subgroup.zpowers_le.2 huI
  have hcomm : ∀ (a : ↥(zpowers u)) (b : ↥Q), α a * β b = β b * α a := by
    intro a b
    have hab : (a : X) * (b : X) = (b : X) * (a : X) := hIQ a (hzI a.2) b b.2
    ext r
    show ((α a (β b r) : ↥R) : X) = ((β b (α a r) : ↥R) : X)
    rw [hαapp, hβapp, hβapp, hαapp]
    calc (a : X) * ((b : X) * (r : X) * (b : X)⁻¹) * (a : X)⁻¹
        = ((a : X) * (b : X)) * (r : X) * ((a : X) * (b : X))⁻¹ := by group
      _ = ((b : X) * (a : X)) * (r : X) * ((b : X) * (a : X))⁻¹ := by rw [hab]
      _ = (b : X) * ((a : X) * (r : X) * (a : X)⁻¹) * (b : X)⁻¹ := by group
  have hA : ¬ p ∣ Nat.card ↥(zpowers u) := by
    rw [Nat.card_zpowers, hu2]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hnfix : ¬ (∀ (a : ↥(zpowers u)) (r : ↥R), (∀ b : ↥Q, β b r = r) → α a r = r) := by
    intro hfix
    have h1 := CFSG.GroupTheory.thompson_A_times_B hRp hA hQp α β hcomm hfix
    obtain ⟨r, hr, hne⟩ := hnc
    have h2 := h1 ⟨u, Subgroup.mem_zpowers u⟩
    have h3 := congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : X)) h2
    simp only [hαapp, MulAut.one_apply] at h3
    apply hne
    have : u * r * u⁻¹ = r := h3
    calc u * r = (u * r * u⁻¹) * u := by group
      _ = r * u := by rw [this]
  obtain ⟨a, r, hrfix, hαr⟩ : ∃ (a : ↥(zpowers u)) (r : ↥R), (∀ b : ↥Q, β b r = r) ∧ α a r ≠ r := by
    by_contra hcon
    apply hnfix
    intro a r hr
    by_contra hne
    exact hcon ⟨a, r, hr, hne⟩
  have hrQ : ∀ q ∈ Q, (q : X) * (r : X) = (r : X) * (q : X) := by
    intro q hq
    have := congrArg (fun φ : ↥R => (φ : X)) (hrfix ⟨q, hq⟩)
    simp only [hβapp] at this
    calc q * (r : X) = (q * (r : X) * q⁻¹) * q := by group
      _ = (r : X) * q := by rw [this]
  have hnu : u * (r : X) ≠ (r : X) * u := by
    intro hcom
    apply hαr
    apply Subtype.ext
    rw [hαapp]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 a.2
    have hcj : u ^ j * (r : X) = (r : X) * u ^ j := (Commute.zpow_left (show Commute u (r : X) from hcom) j).eq
    rw [← hj]
    calc u ^ j * (r : X) * (u ^ j)⁻¹ = ((r : X) * u ^ j) * (u ^ j)⁻¹ := by rw [hcj]
      _ = (r : X) := by group
  have hrO : (r : X) ∈ O := hR.le r.2
  have hrMx : (r : X) ∈ Mx := hCQ r (fun q hq => (hrQ q hq).symm)
  have hcI : u * ((r : X) * u⁻¹ * (r : X)⁻¹) ∈ I := I.mul_mem huI (hIMn r hrMx u⁻¹ (I.inv_mem huI))
  have hcO : u * ((r : X) * u⁻¹ * (r : X)⁻¹) ∈ O := by
    have e : u * ((r : X) * u⁻¹ * (r : X)⁻¹) = (u * (r : X) * u⁻¹) * (r : X)⁻¹ := by group
    rw [e]
    exact O.mul_mem (hOn.conj_mem _ hrO u) (O.inv_mem hrO)
  have hIO : I ⊓ O = ⊥ := by
    apply hIodd (I ⊓ O) inf_le_left
    · rw [Subgroup.inf_subgroupOf_left]
      exact Subgroup.Normal.subgroupOf hOn I
    · exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_right)
  have h1 : u * ((r : X) * u⁻¹ * (r : X)⁻¹) ∈ I ⊓ O := ⟨hcI, hcO⟩
  rw [hIO, Subgroup.mem_bot] at h1
  apply hnu
  calc u * (r : X) = (u * ((r : X) * u⁻¹ * (r : X)⁻¹)) * ((r : X) * u) := by group
    _ = (r : X) * u := by rw [h1, one_mul]

end MainCore

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
