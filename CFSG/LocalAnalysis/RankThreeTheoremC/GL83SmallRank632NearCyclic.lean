module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem NearCyclic.of_surjective {V W : Type*} [Group V] [Group W] [Finite V] (f : V →* W)
    (hf : Function.Surjective f) (h : NearCyclic V) : NearCyclic W := by
  obtain ⟨C, hCc, hC, hCi⟩ := h
  refine ⟨C.map f, ?_, isCyclic_of_surjective (f.subgroupMap C) (f.subgroupMap_surjective C), ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hf w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hCc hc) v]
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (C.index_map_dvd hf)).trans hCi

theorem NearCyclic.of_injective {V W : Type*} [Group V] [Group W] [Finite V] (f : W →* V)
    (hf : Function.Injective f) (h : NearCyclic V) : NearCyclic W := by
  obtain ⟨C, hCc, hC, hCi⟩ := h
  refine ⟨C.comap f, ?_, ?_, ?_⟩
  · intro w hw
    rw [Subgroup.mem_center_iff]
    intro u
    apply hf
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hCc hw) (f u)
  · exact isCyclic_of_injective (f.subgroupComap C)
      fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab))
  · rw [Subgroup.index_comap]
    refine le_trans ?_ hCi
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by
      rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)

theorem NearCyclic.of_mulEquiv {V W : Type*} [Group V] [Group W] [Finite V] (e : W ≃* V)
    (h : NearCyclic V) : NearCyclic W :=
  NearCyclic.of_injective e.toMonoidHom e.injective h

theorem NearCyclic.card_le_eight {V : Type*} [Group V] [Finite V] (h : NearCyclic V)
    (hV : ∀ v : V, v ^ 2 = 1) : Nat.card V ≤ 8 := by
  obtain ⟨C, -, hC, hCi⟩ := h
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hgo : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hV g))
  have hcard : Nat.card C ≤ 2 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd two_pos hgo
  rw [← Subgroup.card_mul_index C]
  calc Nat.card C * C.index ≤ 2 * 4 := Nat.mul_le_mul hcard hCi
    _ = 8 := rfl

private theorem nearCyclic_card_klein :
    Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

private theorem nearCyclic_quaternion_central (q : QuaternionGroup 2)
    (h : ∀ g, g * q = q * g) : q = 1 ∨ q = QuaternionGroup.a 2 := by
  revert q
  decide

private theorem nearCyclic_mem_of_central {G : Type*} [Group G] [Finite G] {A D : Subgroup G}
    (e : A ≃* QuaternionGroup 2) (hDA : D ≤ A) (hD : Nat.card D = 2)
    (hDc : ∀ d ∈ D, ∀ a ∈ A, a * d = d * a) {x : G} (hxA : x ∈ A)
    (hx : ∀ a ∈ A, a * x = x * a) : x ∈ D := by
  have hcentral : ∀ y : A, (∀ a ∈ A, a * (y : G) = (y : G) * a) →
      ∀ g : QuaternionGroup 2, g * e y = e y * g := by
    intro y hy g
    have h : e.symm g * y = y * e.symm g := Subtype.ext (hy (e.symm g : A) (e.symm g).2)
    simpa using congrArg e h
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨d, hd1⟩ := exists_ne (1 : D)
  have hdA : (d : G) ∈ A := hDA d.2
  have hd := nearCyclic_quaternion_central _
    (hcentral ⟨d, hdA⟩ fun a ha => hDc d d.2 a ha)
  have hd' : e ⟨d, hdA⟩ ≠ 1 := by
    intro h
    apply hd1
    have h' : (⟨d, hdA⟩ : A) = 1 := e.injective (by rw [h, map_one])
    exact Subtype.ext (congrArg Subtype.val h' : (d : G) = 1)
  rcases nearCyclic_quaternion_central _ (hcentral ⟨x, hxA⟩ hx) with h | h
  · have h' : (⟨x, hxA⟩ : A) = 1 := e.injective (by rw [h, map_one])
    have hx1 : x = 1 := congrArg Subtype.val h'
    rw [hx1]
    exact D.one_mem
  · have h' : (⟨x, hxA⟩ : A) = ⟨d, hdA⟩ := e.injective (h.trans (hd.resolve_left hd').symm)
    have hxd : x = d := congrArg Subtype.val h'
    rw [hxd]
    exact d.2

private theorem nearCyclic_mem_of_central_sup {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (e : A ≃* QuaternionGroup 2) (hcard : Nat.card (A ⊓ B : Subgroup G) = 2)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hxH : x ∈ A ⊔ B)
    (hx : ∀ w ∈ A ⊔ B, w * x = x * w) : x ∈ B := by
  have hAN : A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (hAB a ha b hb).symm)
  have hzAB : x ∈ (↑(A ⊔ B) : Set G) := hxH
  rw [coe_mul_of_left_le_normalizer_right A B hAN] at hzAB
  obtain ⟨a, ha, b, hb, rfl⟩ := hzAB
  have haD : a ∈ A ⊓ B := by
    refine nearCyclic_mem_of_central e inf_le_left hcard
      (fun d hd a' ha' => hAB a' ha' d hd.2) ha fun a' ha' => ?_
    have h1 := hx a' ((le_sup_left : A ≤ A ⊔ B) ha')
    have h2 := hAB a' ha' b hb
    refine mul_right_cancel (b := b) ?_
    calc a' * a * b = a' * (a * b) := mul_assoc _ _ _
      _ = a * b * a' := h1
      _ = a * (b * a') := mul_assoc _ _ _
      _ = a * (a' * b) := by rw [h2]
      _ = a * a' * b := (mul_assoc _ _ _).symm
  exact B.mul_mem haD.2 hb

private theorem nearCyclic_q8_structure {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {n : ℕ} (h : rankThreeIsQ8CentralCyclic H n) :
    ∃ B : Subgroup G, IsCyclic B ∧ Nat.card B = 2 ^ n ∧ B ≤ H ∧
      (∀ x ∈ H, ∀ b ∈ B, x * b = b * x) ∧ (∀ v ∈ H, (∀ w ∈ H, w * v = v * w) → v ∈ B) ∧
      (B.subgroupOf H).index = 4 := by
  obtain ⟨A, B, ⟨e⟩, hB, hBcard, hAB, rfl, hcard⟩ := h
  have hAV : A ≤ A ⊔ B := le_sup_left
  have hBV : B ≤ A ⊔ B := le_sup_right
  have hcommB : ∀ x ∈ A ⊔ B, ∀ b ∈ B, x * b = b * x := by
    intro x hx b hb
    have hle : A ⊔ B ≤ centralizer ({b} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.mpr (hAB a ha b hb))
      (fun b' hb' => mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm' (⟨b', hb'⟩ : B) ⟨b, hb⟩)))
    exact mem_centralizer_singleton_iff.mp (hle hx)
  refine ⟨B, hB, hBcard, hBV, hcommB,
    fun v hv hc => nearCyclic_mem_of_central_sup e hcard hAB hv hc, ?_⟩
  have hN : (B.subgroupOf (A ⊔ B)).Normal := ⟨fun x hx g => by
    have h : (g : G) * (x : G) * (g : G)⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcommB g g.2 x hx
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ B
    rw [h]
    exact hx⟩
  have h1 := Subgroup.relIndex_sup_right (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B))
  rw [← Subgroup.subgroupOf_sup hAV hBV, subgroupOf_self, relIndex_top_right,
    relIndex_subgroupOf hAV] at h1
  have h2 := Subgroup.relIndex_mul_card B A
  have hA8 : Nat.card A = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [inf_comm, hcard, hA8] at h2
  omega

theorem NearCyclic.of_isKleinOrQ8Central {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h : IsKleinOrQ8Central H) : NearCyclic ↥H := by
  rcases h with h | ⟨n, hn⟩
  · obtain ⟨e⟩ := h
    refine ⟨⊥, bot_le, inferInstance, ?_⟩
    rw [Subgroup.index_bot, Nat.card_congr e.toEquiv, nearCyclic_card_klein]
  · obtain ⟨B, hB, -, hBH, hcomm, -, hidx⟩ := nearCyclic_q8_structure hn
    refine ⟨B.subgroupOf H, ?_, (Subgroup.subgroupOfEquivOfLe hBH).isCyclic.mpr hB, hidx.le⟩
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2 x hx)

private theorem nearCyclic_eq_of_card_four {α : Type*} [Finite α] (hα : Nat.card α = 4)
    (f : α → α) (h3 : ∀ x, f (f (f x)) = x) {x y : α} (hxy : x ≠ y) (hx : f x = x)
    (hy : f y = y) (w : α) : f w = w := by
  classical
  have := Fintype.ofFinite α
  let g : Function.End α := f
  have hg : g ^ 3 = 1 := by
    funext w
    exact h3 w
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := g) (by simpa using hg)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hα] at hmod
  have h2 : 2 ≤ Nat.card (Function.fixedPoints g) := by
    have : ({x, y} : Set α) ⊆ Function.fixedPoints g := by
      rintro _ (rfl | rfl)
      · exact hx
      · exact hy
    have h := Set.ncard_le_ncard this (Set.toFinite _)
    rw [Set.ncard_pair hxy, ← Nat.card_coe_set_eq] at h
    exact h
  have h4 : Nat.card (Function.fixedPoints g) ≤ 4 :=
    hα ▸ Nat.card_le_card_of_injective _ Subtype.val_injective
  have h5 : Nat.card (Function.fixedPoints g) = 4 := by
    unfold Nat.ModEq at hmod
    omega
  by_contra hw
  have := Finite.card_subtype_lt (p := fun x => g x = x) (x := w) hw
  have h6 : Nat.card {x // g x = x} = Nat.card (Function.fixedPoints g) := rfl
  omega

private theorem nearCyclic_aut_trivial {V : Type*} [Group V] (σ : MulAut V) (h3 : σ ^ 3 = 1)
    (Z : Subgroup V) [Finite Z] [IsCyclic Z] {n : ℕ} (hZn : Nat.card Z = 2 ^ n)
    (hσZ : ∀ x ∈ Z, σ x ∈ Z) {x : V} (hx : x ∈ Z) : σ x = x := by
  let f : Z →* Z := (σ.toMonoidHom.comp Z.subtype).codRestrict Z fun x => hσZ x x.2
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (σ.injective (congrArg Subtype.val h))
  let τ : MulAut Z := MulEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ y : Z, (τ y : V) = σ y := fun y => rfl
  have hτ3 : τ ^ 3 = 1 := by
    ext y
    have h := congrArg (fun s : MulAut V => (s y : V)) h3
    simpa [pow_succ, hτ] using h
  have hdvd : orderOf τ ∣ (Nat.card Z).totient := by
    rw [← IsCyclic.card_mulAut Z]
    exact orderOf_dvd_natCard τ
  have hcop : Nat.Coprime 3 (Nat.card Z).totient := by
    rw [hZn]
    rcases n with _ | m
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two m]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right m (by norm_num)) (by norm_num)
  have hord : orderOf τ = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hτ3)) hdvd
  have : τ = 1 := orderOf_eq_one_iff.mp hord
  have h := congrArg (fun s : MulAut Z => (s ⟨x, hx⟩ : V)) this
  exact h

private theorem nearCyclic_aut_eq_one {V : Type*} [Group V] (σ : MulAut V) (h3 : σ ^ 3 = 1)
    (Z : Subgroup V) (hZ : ∀ x : Z, (orderOf x).Coprime 3) (hσ : ∀ x ∈ Z, σ x = x)
    (hq : ∀ v : V, v⁻¹ * σ v ∈ Z) : σ = 1 := by
  ext v
  have hb := hq v
  set b := v⁻¹ * σ v with hbdef
  have hσv : σ v = v * b := by rw [hbdef]; group
  have hσb : σ b = b := hσ b hb
  have h3v : σ (σ (σ v)) = v := by
    have := congrArg (fun s : MulAut V => s v) h3
    simpa [pow_succ] using this
  have hb3 : b ^ 3 = 1 := by
    have h : v * (b * b * b) = v * 1 := by
      calc v * (b * b * b) = σ (σ (σ v)) := by simp only [hσv, map_mul, hσb, mul_assoc]
        _ = v * 1 := by rw [h3v, mul_one]
    have := mul_left_cancel h
    calc b ^ 3 = b * b * b := by rw [pow_succ, sq]
      _ = 1 := this
  have hord : orderOf (⟨b, hb⟩ : Z) = 1 :=
    Nat.Coprime.eq_one_of_dvd (hZ ⟨b, hb⟩) (orderOf_dvd_of_pow_eq_one (Subtype.ext hb3))
  have hb1 : b = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
  show σ v = v
  rw [hσv, hb1, mul_one]

private theorem nearCyclic_fixed_mem {V : Type*} [Group V] [Finite V] (σ : MulAut V)
    (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) (Z : Subgroup V) [Z.Normal] [IsCyclic Z] {n : ℕ}
    (hZn : Nat.card Z = 2 ^ n) (hZi : Z.index = 4) (hσZ : ∀ x ∈ Z, σ x ∈ Z) {v : V}
    (hv : σ v = v) : v ∈ Z := by
  have hσ : ∀ x ∈ Z, σ x = x := fun x hx => nearCyclic_aut_trivial σ h3 Z hZn hσZ hx
  have hcop : ∀ x : Z, (orderOf x).Coprime 3 := fun x =>
    Nat.Coprime.coprime_dvd_left (hZn ▸ orderOf_dvd_natCard x)
      (Nat.Coprime.pow_left n (by norm_num))
  have hbar : ∃ v₀ : V, v₀⁻¹ * σ v₀ ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact h1 (nearCyclic_aut_eq_one σ h3 Z hcop hσ hcon)
  obtain ⟨v₀, hv₀⟩ := hbar
  by_contra hvZ
  let f : V ⧸ Z →* V ⧸ Z := QuotientGroup.map Z Z σ.toMonoidHom fun x hx => hσZ x hx
  have hfmk : ∀ a : V, f (a : V ⧸ Z) = ((σ a : V) : V ⧸ Z) := fun a => rfl
  have hf : ∀ q, f (f (f q)) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      have h3a := congrArg (fun s : MulAut V => s a) h3
      have h3a' : σ (σ (σ a)) = a := by simpa [pow_succ] using h3a
      rw [hfmk, hfmk, hfmk, h3a']
  have hxy : (1 : V ⧸ Z) ≠ (v : V ⧸ Z) := fun h => hvZ (by
    have := QuotientGroup.eq.mp h
    simpa using this)
  have hfix := nearCyclic_eq_of_card_four hZi f hf hxy (map_one f)
    (by rw [hfmk, hv]) (v₀ : V ⧸ Z)
  rw [hfmk] at hfix
  apply hv₀
  have := QuotientGroup.eq.mp hfix
  simpa using Z.inv_mem this

private def nearCyclicConj {G : Type*} [Group G] {V : Subgroup G} {z : G}
    (hz : z ∈ normalizer (V : Set G)) : MulAut V where
  toFun v := ⟨z * v * z⁻¹, (mem_normalizer_iff.mp hz v).mp v.2⟩
  invFun v := ⟨z⁻¹ * v * z, by simpa using (mem_normalizer_iff.mp (inv_mem hz) v).mp v.2⟩
  left_inv v := Subtype.ext (by simp [mul_assoc])
  right_inv v := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem isCyclic_inf_centralizer_of_isKleinOrQ8Central {G : Type*} [Group G] [Finite G]
    {V : Subgroup G} (hV : IsKleinOrQ8Central V) {z : G} (hz : z ^ 3 = 1)
    (hzV : z ∈ normalizer (V : Set G)) (hnc : ¬ V ≤ centralizer ({z} : Set G)) :
    IsCyclic ↥(V ⊓ centralizer ({z} : Set G)) := by
  set σ := nearCyclicConj hzV
  have hσ : ∀ v : V, (σ v : G) = z * v * z⁻¹ := fun v => rfl
  have h3pt : ∀ v : V, σ (σ (σ v)) = v := by
    intro v
    apply Subtype.ext
    rw [hσ, hσ, hσ]
    have hz3 : z * z * z = 1 := by simpa [pow_succ] using hz
    calc z * (z * (z * (v : G) * z⁻¹) * z⁻¹) * z⁻¹ = (z * z * z) * v * (z * z * z)⁻¹ := by group
      _ = v := by rw [hz3]; simp
  have h3 : σ ^ 3 = 1 := by
    ext v
    simpa [pow_succ] using h3pt v
  have h1 : σ ≠ 1 := by
    intro h
    apply hnc
    intro v hv
    rw [mem_centralizer_singleton_iff]
    have h' := congrArg (fun s : MulAut V => (s ⟨v, hv⟩ : G)) h
    have h'' : z * v * z⁻¹ = v := h'
    exact (mul_inv_eq_iff_eq_mul.mp h'').symm
  have hfix : ∀ x (hxV : x ∈ V), x ∈ centralizer ({z} : Set G) → σ ⟨x, hxV⟩ = ⟨x, hxV⟩ := by
    intro x hxV hxc
    apply Subtype.ext
    rw [hσ]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxc).symm
  rcases hV with hV | ⟨n, hn⟩
  · obtain ⟨e⟩ := hV
    have hcard : Nat.card V = 4 := by
      rw [Nat.card_congr e.toEquiv, nearCyclic_card_klein]
    have hbot : V ⊓ centralizer ({z} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxV, hxc⟩
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hxy : (1 : V) ≠ ⟨x, hxV⟩ := fun h => hx1 (congrArg Subtype.val h).symm
      have hall := nearCyclic_eq_of_card_four hcard σ h3pt hxy (map_one σ) (hfix x hxV hxc)
      exact h1 (MulEquiv.ext hall)
    rw [hbot]
    infer_instance
  · obtain ⟨B, hB, hBn, hBV, hcomm, hcen, hidx⟩ := nearCyclic_q8_structure hn
    have hZc : ∀ x ∈ B.subgroupOf V, ∀ y : V, y * x = x * y := fun x hx y =>
      Subtype.ext (hcomm y y.2 x hx)
    have hZnormal : (B.subgroupOf V).Normal := ⟨fun x hx g => by
      have h : g * x * g⁻¹ = x := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hZc x hx g
      rw [h]
      exact hx⟩
    have hZcyc : IsCyclic (B.subgroupOf V) :=
      (Subgroup.subgroupOfEquivOfLe hBV).isCyclic.mpr hB
    have hZn : Nat.card (B.subgroupOf V) = 2 ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBV).toEquiv]
      exact hBn
    have hσZ : ∀ x ∈ B.subgroupOf V, σ x ∈ B.subgroupOf V := by
      intro x hx
      have hc : ∀ y : V, y * σ x = σ x * y := by
        intro y
        have h := hZc x hx (σ⁻¹ y)
        calc y * σ x = σ (σ⁻¹ y) * σ x := by simp
          _ = σ ((σ⁻¹ y) * x) := (map_mul σ _ _).symm
          _ = σ (x * (σ⁻¹ y)) := by rw [h]
          _ = σ x * y := by simp
      exact hcen (σ x) (σ x).2 fun w hw => congrArg Subtype.val (hc ⟨w, hw⟩)
    have hle : V ⊓ centralizer ({z} : Set G) ≤ B := by
      rintro x ⟨hxV, hxc⟩
      exact nearCyclic_fixed_mem σ h3 h1 (B.subgroupOf V) hZn hidx hσZ (hfix x hxV hxc)
    exact Subgroup.isCyclic_of_le hle

end CFSG.LocalAnalysis.RankThreeTheoremC
