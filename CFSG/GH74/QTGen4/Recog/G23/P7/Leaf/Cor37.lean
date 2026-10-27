module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.Cor37C
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
open CFSG.GH74.QTGen4.Recog.G23.P7.Cor37

theorem letter_relations {G : Type} [Group G] (e : Fin 6 → G) (hr : SatisfiesWords g23WordsH e) :
    e 0 * e 0 * e 0 = 1 ∧ e 2 * e 2 * e 2 = 1 ∧ e 4 * e 4 = 1 ∧
      e 4 * e 0 * e 4 * e 0 = 1 ∧ e 4 * e 2 * e 4 * e 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hr [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := hr [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := hr [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := hr [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := hr [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this

theorem card_closure_one_le_three {G : Type} [Group G] [Finite G] (a : G) (ha : a ^ 3 = 1) :
    Nat.card (Subgroup.closure ({1, a} : Set G)) ≤ 3 := by
  have hle : Subgroup.closure ({1, a} : Set G) ≤ Subgroup.zpowers a := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers a
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha
  exact h1.trans (Nat.le_of_dvd (by norm_num) hd)

theorem normH_of_mem_cent {G : Type} [Group G] {M : Subgroup G} {τ g : G}
    (hcC : ∀ c ∈ Subgroup.centralizer ({τ} : Set G), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hg : g ∈ Subgroup.centralizer ({τ} : Set G)) : NormH M (Subgroup.zpowers τ) g where
  conjM m hm := hcC g hg m hm
  conjM' m hm := by
    have := hcC g⁻¹ (Subgroup.inv_mem _ hg) m hm
    simpa using this
  conjP p hp := by
    have hc : g * τ = τ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have := mem_zpowers_commute hc hp
    rw [this]
    simpa using hp
  conjP' p hp := by
    have hc : g * τ = τ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hc' : g⁻¹ * τ = τ * g⁻¹ := by
      calc g⁻¹ * τ = g⁻¹ * (τ * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * τ) * g⁻¹ := by rw [hc]
        _ = τ * g⁻¹ := by group
    have := mem_zpowers_commute hc' hp
    rw [this]
    simpa using hp

theorem normH_of_inverts {G : Type} [Group G] {M : Subgroup G} {τ g : G}
    (hgM : ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hgM' : ∀ m ∈ M, g⁻¹ * m * g ∈ M)
    (hgτ : g * τ * g⁻¹ = τ⁻¹) : NormH M (Subgroup.zpowers τ) g where
  conjM := hgM
  conjM' := hgM'
  conjP p hp := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← conj_zpow, hgτ]
    have e : (τ⁻¹) ^ k = τ ^ (-k) := by rw [zpow_neg, inv_zpow]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers τ) (-k)
  conjP' p hp := by
    have h1 : τ = g⁻¹ * τ⁻¹ * g := by
      rw [← hgτ]
      group
    have hgτ' : g⁻¹ * τ * g = τ⁻¹ := by
      calc g⁻¹ * τ * g = (g⁻¹ * τ⁻¹ * g)⁻¹ := by group
        _ = τ⁻¹ := by rw [← h1]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have e2 : (g⁻¹ * τ * g) ^ k = g⁻¹ * τ ^ k * g := by
      have := conj_zpow (a := g⁻¹) (b := τ) (i := k)
      simpa using this
    rw [← e2, hgτ']
    have e : (τ⁻¹) ^ k = τ ^ (-k) := by rw [zpow_neg, inv_zpow]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers τ) (-k)

theorem card_inf_cent_eq {G : Type} [Group G] (M : Subgroup G) (σ : G) :
    Nat.card ↥(M ⊓ Subgroup.centralizer ({σ} : Set G)) =
      Nat.card {x : ↥M // (x : G) * σ = σ * (x : G)} := by
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subgroup.mem_centralizer_singleton_iff.mp x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem cor37_setup {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e) :
    (∀ y : G, y ∈ H ↔ y * zOf e = zOf e * y) ∧ zOf e ∈ H₁ ∧ zOf e ∈ H₂ ∧ zOf e ≠ 1 ∧
      zOf e * zOf e = 1 ∧ e 0 ∈ H₁ ∧ e 2 ∈ H₂ ∧ e 0 ≠ 1 ∧ e 2 ≠ 1 ∧
      e 0 * e 2 = e 2 * e 0 ∧ e 0 * e 0 * e 0 = 1 ∧ e 2 * e 2 * e 2 = 1 := by
  classical
  obtain ⟨r30, r32, r4, r40, r42⟩ := letter_relations e h.lets.rels
  have he0H₁ : e 0 ∈ H₁ := by
    rw [← h.lets.gen₁]
    exact Subgroup.subset_closure (by simp)
  have he1H₁ : e 1 ∈ H₁ := by
    rw [← h.lets.gen₁]
    exact Subgroup.subset_closure (by simp)
  have he2H₂ : e 2 ∈ H₂ := by
    rw [← h.lets.gen₂]
    exact Subgroup.subset_closure (by simp)
  have hz1H₁ : zOf e ∈ H₁ := by
    unfold zOf
    exact pow_mem (mul_mem he0H₁ he1H₁) 2
  have hz2H₂ : zOf e ∈ H₂ := by
    have hmem : zOf e ∈ Subgroup.centralizer ({e 2} : Set G) ⊓ H₂ := by
      rw [hF.centL₂]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact hmem.2
  have hH_eq : H = Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) :=
    h.ctx.one.eq_centralizer
  have hH1H2 : Nat.card ↥(H₁ ⊓ H₂) = 2 := h.ctx.one.card_inf
  obtain ⟨y₀, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(H₁ ⊓ H₂))).mp hH1H2
  have hz1 : zOf e ≠ 1 := by
    intro hz
    have h2G : 2 ∣ Nat.card G := by
      have h576 : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
      rw [hF.card_H] at h576
      exact (by norm_num : 2 ∣ 576).trans h576
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2G
    have hc := hO u hu
    rw [hz] at hc
    rw [isConj_one_right] at hc
    rw [hc, orderOf_one] at hu
    norm_num at hu
  have hxcases : ∀ x ∈ H₁ ⊓ H₂, x = 1 ∨ x = zOf e := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have hzmem : zOf e ∈ H₁ ⊓ H₂ := ⟨hz1H₁, hz2H₂⟩
      have e1 : (⟨x, hx⟩ : ↥(H₁ ⊓ H₂)) = y₀ :=
        huniq _ (fun e' => hx1 (congrArg Subtype.val e'))
      have e2 : (⟨zOf e, hzmem⟩ : ↥(H₁ ⊓ H₂)) = y₀ :=
        huniq _ (fun e' => hz1 (congrArg Subtype.val e'))
      exact congrArg Subtype.val (e1.trans e2.symm)
  have hHC : ∀ y : G, y ∈ H ↔ y * zOf e = zOf e * y := by
    intro y
    rw [hH_eq, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy
      exact (hy (zOf e) ⟨hz1H₁, hz2H₂⟩).symm
    · intro hy x hx
      rcases hxcases x hx with rfl | rfl
      · simp
      · exact hy.symm
  have hzz : zOf e * zOf e = 1 := by
    obtain ⟨φ₁⟩ := h.ctx.one.iso_one
    exact sq_one_of_central_L H₁ φ₁ (zOf e) hz1H₁ hz1
      (fun g hg => (hHC g).mp (h.ctx.one.le_one hg))
  have he0ne : e 0 ≠ 1 := by
    intro h0
    have hc := hF.card_P
    unfold Psub at hc
    rw [h0] at hc
    have := card_closure_one_le_three (e 2) (by rw [pow_three']; exact r32)
    omega
  have he2ne : e 2 ≠ 1 := by
    intro h2
    have hc := hF.card_P
    unfold Psub at hc
    rw [h2, Set.pair_comm] at hc
    have := card_closure_one_le_three (e 0) (by rw [pow_three']; exact r30)
    omega
  have he02 : e 0 * e 2 = e 2 * e 0 := by
    have hX : (e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2 = 1 := by
      have := h.lets.rels [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
      simpa [FreeGroup.lift_mk, mul_assoc] using this
    calc e 0 * e 2 = e 2 * e 0 * ((e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2) := by group
      _ = e 2 * e 0 := by rw [hX, mul_one]
  exact ⟨hHC, hz1H₁, hz2H₂, hz1, hzz, he0H₁, he2H₂, he0ne, he2ne, he02, r30, r32⟩

theorem vertex_card_of {G : Type} [Group G] [Finite G] {H H₁ H₂ M L : Subgroup G} {e : Fin 6 → G}
    {τ σ t : G} (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hHC : ∀ y : G, y ∈ H ↔ y * zOf e = zOf e * y)
    (hτ3 : orderOf τ = 3) (hinfH : M ⊓ H = Subgroup.zpowers τ)
    (hcompl : IsCentComplement (Subgroup.centralizer ({τ} : Set G)) L M)
    (hthree : IsPGroup 3 M) (hLH : L ≤ H) (hzL : zOf e ∈ L) (hz1 : zOf e ≠ 1)
    (hzz : zOf e * zOf e = 1) (φ : L ≃* SL23) (hσL : σ ∈ L) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (htH : t ∈ H) (htt : t * t = 1) (htτ : t * τ * t⁻¹ = τ⁻¹) (ht1 : t ≠ 1)
    (htz1 : t * zOf e ≠ 1) (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (hM : Nat.card M = 3 * Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) ^ 2)
    (hc : Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 1 ∨
      Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 3 ∨
      Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 9)
    (hc' : Nat.card ↥(M ⊓ Subgroup.centralizer ({t * zOf e} : Set G)) =
      Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G))) :
    Nat.card ↥(M ⊓ Subgroup.centralizer ({σ} : Set G)) =
      3 * Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hτM : τ ∈ M := by
    have : τ ∈ M ⊓ H := by
      rw [hinfH]
      exact Subgroup.mem_zpowers τ
    exact this.1
  have hτc : ∀ k ∈ L, k * τ = τ * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcompl.right_le hk)
  have hcentM : ∀ m ∈ M, m * τ = τ * m := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mp (hcompl.left_le hm)
  have hτH : τ ∈ H := by
    have : τ ∈ M ⊓ H := by
      rw [hinfH]
      exact Subgroup.mem_zpowers τ
    exact this.2
  have hzτ : zOf e * τ = τ * zOf e := ((hHC τ).mp hτH).symm
  have hzH : zOf e ∈ H := hLH hzL
  have hzc : ∀ g ∈ L, g * zOf e = zOf e * g := fun g hg => (hHC g).mp (hLH hg)
  have hCz : ∀ x ∈ M, zOf e * x * (zOf e)⁻¹ = x → x ∈ Subgroup.zpowers τ := by
    intro x hx hzx
    have hxz : x * zOf e = zOf e * x := by
      calc x * zOf e = (zOf e * x * (zOf e)⁻¹) * zOf e := by rw [hzx]
        _ = zOf e * x := by group
    have hxH : x ∈ H := (hHC x).mpr hxz
    have : x ∈ M ⊓ H := ⟨hx, hxH⟩
    rw [hinfH] at this
    exact this
  have hLn : ∀ k ∈ L, NormH M (Subgroup.zpowers τ) k := fun k hk =>
    normH_of_mem_cent (fun c hc' m hm => hcompl.conj_mem c hc' m hm)
      (Subgroup.mem_centralizer_singleton_iff.mpr (hτc k hk))
  have hzn : NormH M (Subgroup.zpowers τ) (zOf e) :=
    normH_of_mem_cent (fun c hc' m hm => hcompl.conj_mem c hc' m hm)
      (Subgroup.mem_centralizer_singleton_iff.mpr hzτ)
  have hcomm_P : ∀ m ∈ M, ∀ p ∈ Subgroup.zpowers τ, m * p = p * m := fun m hm p hp =>
    mem_zpowers_commute (hcentM m hm) hp
  haveI : ((Subgroup.zpowers τ).subgroupOf M).Normal :=
    normal_subgroupOf_of_central M (Subgroup.zpowers τ) hcomm_P
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ht_norm : NormH M (Subgroup.zpowers τ) t := by
    refine normH_of_inverts (fun m hm => htM m hm) (fun m hm => ?_) htτ
    have := htM m hm
    rw [htinv] at this ⊢
    exact this
  have htz : t * zOf e = zOf e * t := (hHC t).mp htH
  have htz2 : (t * zOf e) * (t * zOf e) = 1 := by
    calc (t * zOf e) * (t * zOf e) = t * (zOf e * t) * zOf e := by group
      _ = t * (t * zOf e) * zOf e := by rw [← htz]
      _ = (t * t) * (zOf e * zOf e) := by group
      _ = 1 := by rw [htt, hzz, mul_one]
  have hord_t : orderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hord_tz : orderOf (t * zOf e) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact htz2) htz1
  have hexpt : Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 9 →
      ∀ x : ↥M, t * (x : G) * t⁻¹ = (x : G) → x ^ 3 = 1 := by
    intro h9 x hx
    have hxC : (x : G) ∈ M ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have htx : t * (x : G) = (x : G) * t := by
        calc t * (x : G) = (t * (x : G) * t⁻¹) * t := by group
          _ = (x : G) * t := by rw [hx]
      exact htx.symm
    have h3 := pow_three_of_card_nine_cent hF hO hHC t (M ⊓ Subgroup.centralizer ({t} : Set G))
      inf_le_right h9 hord_t (x : G) hxC
    apply Subtype.ext
    simpa using h3
  have hexptz : Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G)) = 9 →
      ∀ x : ↥M, (t * zOf e) * (x : G) * (t * zOf e)⁻¹ = (x : G) → x ^ 3 = 1 := by
    intro h9 x hx
    have hxC : (x : G) ∈ M ⊓ Subgroup.centralizer ({t * zOf e} : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have htx : (t * zOf e) * (x : G) = (x : G) * (t * zOf e) := by
        calc (t * zOf e) * (x : G) = ((t * zOf e) * (x : G) * (t * zOf e)⁻¹) * (t * zOf e) := by
              group
          _ = (x : G) * (t * zOf e) := by rw [hx]
      exact htx.symm
    have hcard : Nat.card ↥(M ⊓ Subgroup.centralizer ({t * zOf e} : Set G)) = 9 := by
      rw [hc', h9]
    have h3 := pow_three_of_card_nine_cent hF hO hHC (t * zOf e)
      (M ⊓ Subgroup.centralizer ({t * zOf e} : Set G)) inf_le_right hcard hord_tz (x : G) hxC
    apply Subtype.ext
    simpa using h3
  have hσn := hLn σ hσL
  have key := vertex_count (G := G) (M := M) (τ := τ) (z := zOf e) (σ := σ) (t := t) (L := L)
    (c := Nat.card ↥(M ⊓ Subgroup.centralizer ({t} : Set G))) hτM hcentM hτ3 hM hc φ hLn hzz hzL
    hz1 hzc hzτ hCz (fun k hk => hτc k hk) hσL hσ3 hσ1 htt htz htz2 ht_norm hexpt hexptz
  rw [card_inf_cent_eq M σ]
  exact key

theorem cor37_core {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hv₁ : VertexCore e H (e 0) H₂ M₁) (hv₂ : VertexCore e H (e 2) H₁ M₂)
    (hpb : PbarCore e Pb) : Cor37 e M₁ M₂ Pb := by
  classical
  obtain ⟨hHC, hz1H₁, hz2H₂, hz1, hzz, he0H₁, he2H₂, he0ne, he2ne, he02, r30, r32⟩ :=
    cor37_setup h hF hO
  obtain ⟨r30', r32', r4, r40, r42⟩ := letter_relations e h.lets.rels
  obtain ⟨φ₁⟩ := h.ctx.one.iso_one
  obtain ⟨φ₂⟩ := h.ctx.one.iso_two
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ30 : orderOf (e 0) = 3 := orderOf_eq_prime (by rw [pow_three']; exact r30) he0ne
  have hσ32 : orderOf (e 2) = 3 := orderOf_eq_prime (by rw [pow_three']; exact r32) he2ne
  have hσ30' : (e 0) ^ 3 = 1 := by rw [pow_three']; exact r30
  have hσ32' : (e 2) ^ 3 = 1 := by rw [pow_three']; exact r32
  have he4H : e 4 ∈ H := by
    rw [← h.lets.gen]
    exact Subgroup.subset_closure ⟨4, rfl⟩
  have he1H₁ : e 1 ∈ H₁ := by
    rw [← h.lets.gen₁]
    exact Subgroup.subset_closure (by simp)
  have he3H₂ : e 3 ∈ H₂ := by
    rw [← h.lets.gen₂]
    exact Subgroup.subset_closure (by simp)
  have hK : e 4 ∉ H₁ ⊔ H₂ := by
    intro hK4
    have hle : H ≤ H₁ ⊔ H₂ := by
      rw [← h.lets.gen]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.mem_sup_left he0H₁
      · exact Subgroup.mem_sup_left he1H₁
      · exact Subgroup.mem_sup_right he2H₂
      · exact Subgroup.mem_sup_right he3H₂
      · exact hK4
    have h1 := Subgroup.relIndex_eq_one.mpr hle
    rw [h.ctx.one.index] at h1
    norm_num at h1
  have ht1 : e 4 ≠ 1 := by
    intro h1
    apply hK
    rw [h1]
    exact (H₁ ⊔ H₂).one_mem
  have htz1 : e 4 * zOf e ≠ 1 := by
    intro h1
    apply hK
    have h4 : e 4 = zOf e := by
      calc e 4 = e 4 * zOf e * zOf e := by rw [mul_assoc, hzz, mul_one]
        _ = 1 * zOf e := by rw [h1]
        _ = zOf e := one_mul _
    rw [h4]
    exact Subgroup.mem_sup_left hz1H₁
  have hinv4 : (e 4)⁻¹ = e 4 := inv_eq_of_mul_eq_one_right r4
  have htτ0 : e 4 * e 0 * (e 4)⁻¹ = (e 0)⁻¹ := by
    rw [hinv4]
    exact eq_inv_of_mul_eq_one_left r40
  have htτ2 : e 4 * e 2 * (e 4)⁻¹ = (e 2)⁻¹ := by
    rw [hinv4]
    exact eq_inv_of_mul_eq_one_left r42
  have he0H : e 0 ∈ H := h.ctx.one.le_one he0H₁
  have he2H : e 2 ∈ H := h.ctx.one.le_two he2H₂
  have hcomm_z0 : e 0 * zOf e = zOf e * e 0 := (hHC (e 0)).mp he0H
  have hcomm_z2 : e 2 * zOf e = zOf e * e 2 := (hHC (e 2)).mp he2H
  have hcentL₁ : ∀ l ∈ H₁, l * e 0 = e 0 * l →
      l ∈ Subgroup.zpowers (e 0) ⊔ Subgroup.zpowers (zOf e) := by
    intro l hl hlc
    have hmem : l ∈ Subgroup.centralizer ({e 0} : Set G) ⊓ H₁ :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hlc, hl⟩
    rw [hF.centL₁] at hmem
    exact hmem
  have hcentL₂ : ∀ l ∈ H₂, l * e 2 = e 2 * l →
      l ∈ Subgroup.zpowers (e 2) ⊔ Subgroup.zpowers (zOf e) := by
    intro l hl hlc
    have hmem : l ∈ Subgroup.centralizer ({e 2} : Set G) ⊓ H₂ :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hlc, hl⟩
    rw [hF.centL₂] at hmem
    exact hmem
  have hA₂ := vertex_card_of hF hO hHC hσ32 hv₂.inf_H hv₂.compl hv₂.three h.ctx.one.le_one
    hz1H₁ hz1 hzz φ₁ he0H₁ hσ30' he0ne he4H r4 htτ2 ht1 htz1 hv₂.conj_t hv₂.card_eq
    hv₂.card_cent hv₂.card_cent'
  have hA₁ := vertex_card_of hF hO hHC hσ30 hv₁.inf_H hv₁.compl hv₁.three h.ctx.one.le_two
    hz2H₂ hz1 hzz φ₂ he2H₂ hσ32' he2ne he4H r4 htτ0 ht1 htz1 hv₁.conj_t hv₁.card_eq
    hv₁.card_cent hv₁.card_cent'
  have hPgen₂ : Psub e = Subgroup.closure ({e 0, e 2} : Set G) := rfl
  have hPgen₁ : Psub e = Subgroup.closure ({e 2, e 0} : Set G) := by
    unfold Psub
    rw [Set.pair_comm]
  have cardPbM₂ := card_pb_eq hσ30 hPgen₂ hpb.compl hpb.P_le hv₂.compl hv₂.three he0H₁
    hz1H₁ hcentL₁ hzz he02 hcomm_z0 hcomm_z2.symm
  have cardPbM₁ := card_pb_eq hσ32 hPgen₁ hpb.compl hpb.P_le hv₁.compl hv₁.three he2H₂
    hz2H₂ hcentL₂ hzz he02.symm hcomm_z2 hcomm_z0.symm
  have hPb₂ := pb_eq_sup hPgen₂ hpb.compl hpb.P_le hv₂.compl hv₂.three he0H₁ hz1H₁ hcentL₁ hzz
    he02 hcomm_z0 hcomm_z2.symm
  have hPb₁ := pb_eq_sup hPgen₁ hpb.compl hpb.P_le hv₁.compl hv₁.three he2H₂ hz2H₂ hcentL₂ hzz
    he02.symm hcomm_z2 hcomm_z0.symm
  have hc₁ := hv₁.card_cent
  have hc₂ := hv₂.card_cent
  have hM₁ := hv₁.card_eq
  have hM₂ := hv₂.card_eq
  have cardPb9₂ : Nat.card ↥Pb = 3 * (3 * Nat.card ↥(M₂ ⊓ Subgroup.centralizer ({e 4} : Set G))) := by
    rw [cardPbM₂, hA₂]
  have cardPb9₁ : Nat.card ↥Pb = 3 * (3 * Nat.card ↥(M₁ ⊓ Subgroup.centralizer ({e 4} : Set G))) := by
    rw [cardPbM₁, hA₁]
  have hc12 : Nat.card ↥(M₁ ⊓ Subgroup.centralizer ({e 4} : Set G)) =
      Nat.card ↥(M₂ ⊓ Subgroup.centralizer ({e 4} : Set G)) := by
    have heq9 := cardPb9₁.symm.trans cardPb9₂
    omega
  refine
    { card_eq := ?_
      cases := ?_
      card_Pb₁ := cardPbM₂
      card_Pb₂ := cardPbM₁
      Pb_eq₁ := hPb₂
      Pb_eq₂ := hPb₁ }
  · rw [hM₁, hM₂, hc12]
  · rw [hM₁, hc12]
    rcases hc₂ with h1 | h3 | h9
    · left
      constructor
      · rw [h1] <;> norm_num
      · rw [cardPb9₂, h1] <;> norm_num
    · right
      left
      constructor
      · rw [h3] <;> norm_num
      · rw [cardPb9₂, h3] <;> norm_num
    · right
      right
      constructor
      · rw [h9] <;> norm_num
      · rw [cardPb9₂, h9] <;> norm_num

theorem leafCor37 : LeafCor37 := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb h hF hO hv₁ hv₂ hpb
  exact cor37_core h hF hO hv₁ hv₂ hpb

end CFSG.GH74.QTGen4.Recog.G23.P7
