module

public import CFSG.GH74.GLS.Bg.Statements

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg

theorem eq_of_normalizer_eq_pGroup {G : Type*} [Group G] [Finite G] {P Y : Subgroup G} (r : ℕ)
    [Fact r.Prime] (hP : IsPGroup r P) (hYP : Y ≤ P)
    (hN : ∀ x ∈ P, x ∈ normalizer (Y : Set G) → x ∈ Y) : Y = P := by
  by_contra hne
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : Y.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    apply le_antisymm hYP
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ Y.subgroupOf P := by rw [h]; trivial
    exact this
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := ↥P) (Y.subgroupOf P) hlt
  obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt hgrow
  apply hxn
  have hxG : (x : G) ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have hnP : n ∈ P := hYP hn
      exact (mem_normalizer_iff.mp hx ⟨n, hnP⟩).mp hn
    · intro hn
      have hxnx : (x : G) * n * (x : G)⁻¹ ∈ P := hYP hn
      have hnP : n ∈ P := by
        have : (x : G)⁻¹ * ((x : G) * n * (x : G)⁻¹) * (x : G) ∈ P :=
          P.mul_mem (P.mul_mem (P.inv_mem x.2) hxnx) x.2
        simpa [mul_assoc] using this
      exact (mem_normalizer_iff.mp hx ⟨n, hnP⟩).mpr hn
  exact hN x x.2 hxG

@[expose] def conjRestrict {G : Type} [Group G] (B : Subgroup G) (c : G)
    (hc : ∀ b ∈ B, c * b * c⁻¹ ∈ B) (hc' : ∀ b ∈ B, c⁻¹ * b * c ∈ B) : ↥B ≃* ↥B where
  toFun b := ⟨c * b * c⁻¹, hc b b.2⟩
  invFun b := ⟨c⁻¹ * b * c, hc' b b.2⟩
  left_inv b := by ext; simp [mul_assoc]
  right_inv b := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem Op_conj_mem {G : Type} [Group G] {C B : Subgroup G} (r : ℕ)
    (hBnorm : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B) {c : G} (hc : c ∈ C) {y : G} (hy : y ∈ Op r B) :
    c * y * c⁻¹ ∈ Op r B := by
  obtain ⟨y', hy', rfl⟩ := hy
  set φ := conjRestrict B c (hBnorm c hc) (fun b hb => by
    simpa using hBnorm c⁻¹ (C.inv_mem hc) b hb) with hφ
  have hchar := (pCore_characteristic (p := r) (G := ↥B)).fixed φ
  have hmem : φ y' ∈ pCore r ↥B := by
    have : y' ∈ (pCore r ↥B).comap φ.toMonoidHom := by rw [hchar]; exact hy'
    exact this
  exact ⟨φ y', hmem, rfl⟩

theorem le_Op_of_normalized {G : Type} [Group G] [Finite G] {B W : Subgroup G} (r : ℕ)
    (hWB : W ≤ B) (hnorm : ∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W) (hW : IsPGroup r W) :
    W ≤ Op r B := by
  have hn : (W.subgroupOf B).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hp : IsPGroup r ↥(W.subgroupOf B) := by
    have := hW.of_equiv (subgroupOfEquivOfLe hWB).symm
    exact this
  have hle : W.subgroupOf B ≤ pCore r ↥B := le_sSup ⟨hn, hp⟩
  intro w hw
  exact ⟨⟨w, hWB hw⟩, hle (by rw [mem_subgroupOf]; exact hw), rfl⟩

theorem isPGroup_Op {G : Type} [Group G] [Finite G] (r : ℕ) (B : Subgroup G) :
    IsPGroup r (Op r B) :=
  (pCore_isPGroup (p := r) (G := ↥B)).of_equiv (Subgroup.equivMapOfInjective _ B.subtype B.subtype_injective)

theorem core_growth {G : Type} [Group G] [Finite G] {Ĉ B H X : Subgroup G} (r : ℕ) [Fact r.Prime]
    (hcoat : IsCoatom Ĉ) (hsimple : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤)
    (hBC : B ≤ Ĉ) (hBnorm : ∀ c ∈ Ĉ, ∀ b ∈ B, c * b * c⁻¹ ∈ B) (hBH : B ≤ H)
    (hXH : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hX : IsPGroup r X)
    (hD : ∀ x ∈ X, x ∈ Ĉ → x ∈ B) :
    (Op r B = ⊥ ∧ X ⊓ Ĉ = ⊥) ∨ (Op r B ≠ ⊥ ∧ X ≤ Op r B) := by
  have hWB : X ⊓ Ĉ ≤ B := fun x hx => hD x hx.1 hx.2
  have hWnorm : ∀ b ∈ B, ∀ w ∈ X ⊓ Ĉ, b * w * b⁻¹ ∈ X ⊓ Ĉ := fun b hb w hw =>
    ⟨hXH b (hBH hb) w hw.1, Ĉ.mul_mem (Ĉ.mul_mem (hBC hb) hw.2) (Ĉ.inv_mem (hBC hb))⟩
  have hWp : IsPGroup r (X ⊓ Ĉ : Subgroup G) := hX.to_inf_left
  have hWY : X ⊓ Ĉ ≤ Op r B := le_Op_of_normalized r hWB hWnorm hWp
  by_cases hY : Op r B = ⊥
  · left
    exact ⟨hY, le_bot_iff.mp (hY ▸ hWY)⟩
  · right
    refine ⟨hY, ?_⟩
    have hYB : Op r B ≤ B := Subgroup.map_subtype_le _
    have hYnorm : ∀ c ∈ Ĉ, ∀ y ∈ Op r B, c * y * c⁻¹ ∈ Op r B :=
      fun c hc y hy => Op_conj_mem r hBnorm hc hy
    have hnormC : Ĉ ≤ normalizer ((Op r B : Subgroup G) : Set G) := fun c hc => by
      rw [mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hYnorm c hc n hn
      · intro hn
        have := hYnorm c⁻¹ (Ĉ.inv_mem hc) _ hn
        simpa [mul_assoc] using this
    have hNY : normalizer ((Op r B : Subgroup G) : Set G) = Ĉ := by
      by_contra hne
      have hlt : Ĉ < normalizer ((Op r B : Subgroup G) : Set G) :=
        lt_of_le_of_ne hnormC (Ne.symm hne)
      have htop : normalizer ((Op r B : Subgroup G) : Set G) = ⊤ := hcoat.2 _ hlt
      have hYn : (Op r B).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hg : g ∈ normalizer ((Op r B : Subgroup G) : Set G) := by rw [htop]; trivial
        exact (mem_normalizer_iff.mp hg n).mp hn
      rcases hsimple _ hYn with h | h
      · exact hY h
      · exact hcoat.1 (eq_top_iff.mpr (fun x _ => hBC (hYB (h ▸ (Subgroup.mem_top x)))))
    have hYnX : Op r B ≤ normalizer (X : Set G) := fun y hy => by
      rw [mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hXH y (hBH (hYB hy)) n hn
      · intro hn
        have := hXH y⁻¹ (H.inv_mem (hBH (hYB hy))) _ hn
        simpa [mul_assoc] using this
    have hPp : IsPGroup r (X ⊔ Op r B : Subgroup G) :=
      hX.to_sup_of_normal_left' (isPGroup_Op r B) hYnX
    have hEq : Op r B = X ⊔ Op r B := by
      refine eq_of_normalizer_eq_pGroup r hPp le_sup_right ?_
      intro p hp hpn
      have hset := Subgroup.coe_mul_of_right_le_normalizer_left X (Op r B) hYnX
      have hp' : p ∈ ((X ⊔ Op r B : Subgroup G) : Set G) := hp
      rw [hset] at hp'
      obtain ⟨x, hx, y, hy, rfl⟩ := hp'
      have hxn : x ∈ normalizer ((Op r B : Subgroup G) : Set G) := by
        have hyn : y ∈ normalizer ((Op r B : Subgroup G) : Set G) :=
          Subgroup.le_normalizer hy
        have := (Subgroup.normalizer ((Op r B : Subgroup G) : Set G)).mul_mem hpn
          ((normalizer ((Op r B : Subgroup G) : Set G)).inv_mem hyn)
        simpa [mul_assoc] using this
      have hxC : x ∈ Ĉ := hNY ▸ hxn
      have hxY : x ∈ Op r B := hWY ⟨hx, hxC⟩
      exact (Op r B).mul_mem hxY hy
    exact hEq ▸ le_sup_left

theorem Fm_conj_mem {G : Type} [Group G] (H : Subgroup G) {c : G} (hc : c ∈ H) {b : G}
    (hb : b ∈ Fm H) : c * b * c⁻¹ ∈ Fm H := by
  obtain ⟨b', hb', rfl⟩ := hb
  have := fittingSubgroup_normal.conj_mem b' hb' ⟨c, hc⟩
  exact ⟨⟨c, hc⟩ * b' * ⟨c, hc⟩⁻¹, this, rfl⟩

theorem Fm_isNilpotent {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Group.IsNilpotent ↥(Fm H) :=
  Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem mem_Op_of_orderOf_prime {G : Type} [Group G] [Finite G] {F : Subgroup G}
    (hF : Group.IsNilpotent ↥F) {r : ℕ} [Fact r.Prime] {e : G} (he : e ∈ F) (hord : orderOf e = r) :
    e ∈ Op r F := by
  set e' : ↥F := ⟨e, he⟩ with he'
  have hord' : orderOf e' = r := by rw [← hord]; exact Subgroup.orderOf_mk e he
  have hz : IsPGroup r (Subgroup.zpowers e') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord']; simp)
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  have hnormal := Group.IsNilpotent.sylow_normal hF r P
  have hle : (P : Subgroup ↥F) ≤ pCore r ↥F := le_sSup ⟨hnormal, P.isPGroup'⟩
  exact ⟨e', hle (hP (Subgroup.mem_zpowers e')), rfl⟩

theorem Op_le_pPrimeCoreOf {G : Type} [Group G] [Finite G] (F : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) : Op p F ≤ pPrimeCoreOf 2 F := by
  have : Fact p.Prime := ⟨hp⟩
  apply Subgroup.map_mono
  refine le_sSup ⟨pCore_normal, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := p) (G := ↥F))
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem odd_orderOf_of_mem_pPrimeCoreOf {G : Type} [Group G] [Finite G] {F : Subgroup G} {e : G}
    (he : e ∈ pPrimeCoreOf 2 F) : Odd (orderOf e) := by
  obtain ⟨e', he', rfl⟩ := he
  have hd : orderOf (⟨e', he'⟩ : ↥(pPrimeCore 2 ↥F)) ∣ Nat.card ↥(pPrimeCore 2 ↥F) :=
    orderOf_dvd_natCard _
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥F)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥F))
  have h1 := Odd.of_dvd_nat hodd hd
  rw [Subgroup.orderOf_mk] at h1
  show Odd (orderOf (e' : G))
  rwa [Subgroup.orderOf_coe]

theorem inverted_of_fixed_point_free {G : Type} [Group G] [Finite G] {E : Subgroup G} {t : G}
    (ht2 : t * t = 1) (hnorm : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hfix : ∀ e ∈ E, t * e * t⁻¹ = e → e = 1) : ∀ e ∈ E, t * e * t⁻¹ = e⁻¹ := by
  let φ : ↥E → ↥E := fun a =>
    ⟨(a : G)⁻¹ * (t * a * t⁻¹), E.mul_mem (E.inv_mem a.2) (hnorm a a.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h : a⁻¹ * (t * a * t⁻¹) = b⁻¹ * (t * b * t⁻¹) := congrArg Subtype.val hab
    have h1 : b * a⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by
      calc b * a⁻¹ = b * (a⁻¹ * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
        _ = b * (b⁻¹ * (t * b * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [h]
        _ = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by group
    have hc : t * (b * a⁻¹) * t⁻¹ = b * a⁻¹ := by
      calc t * (b * a⁻¹) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ := by group
        _ = b * a⁻¹ := h1.symm
    have hmem : b * a⁻¹ ∈ E := E.mul_mem hb (E.inv_mem ha)
    have := hfix _ hmem hc
    exact Subtype.ext (mul_inv_eq_one.mp this).symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro e he
  obtain ⟨a, ha⟩ := hsurj ⟨e, he⟩
  have h : (a : G)⁻¹ * (t * a * t⁻¹) = e := congrArg Subtype.val ha
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [← h]
  rw [hti]
  calc t * ((a : G)⁻¹ * (t * a * t)) * t = t * (a : G)⁻¹ * t * a * (t * t) := by group
    _ = (a⁻¹ * (t * a * t))⁻¹ := by
      rw [ht2]
      simp [mul_assoc, hti]

theorem Fpi_odd_inverted {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} (htH : t ∈ H)
    (ht2 : t * t = 1)
    (hfix : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ x ∈ Op r (Fm H), t * x * t⁻¹ = x → x = 1) :
    ∀ e ∈ Fpi {r : ℕ | r.Prime ∧ r ≠ 2} H, t * e * t⁻¹ = e⁻¹ := by
  set E := Fpi {r : ℕ | r.Prime ∧ r ≠ 2} H with hE
  have hEle : E ≤ pPrimeCoreOf 2 (Fm H) :=
    iSup₂_le fun p hp => Op_le_pPrimeCoreOf (Fm H) p hp.1 hp.2
  have hEF : E ≤ Fm H := iSup₂_le fun p _ => Subgroup.map_subtype_le _
  have hnorm : ∀ e ∈ E, t * e * t⁻¹ ∈ E := by
    intro e he
    have : E ≤ E.comap (MulAut.conj t).toMonoidHom := iSup₂_le fun p hp x hx => by
      show t * x * t⁻¹ ∈ E
      exact (le_iSup₂ (f := fun p (_ : p ∈ {r : ℕ | r.Prime ∧ r ≠ 2}) => Op p (Fm H)) p hp)
        (Op_conj_mem p (fun c hc b hb => Fm_conj_mem H hc hb) htH hx)
    exact this he
  refine inverted_of_fixed_point_free ht2 hnorm ?_
  intro e he hte
  by_contra hne
  have hord : orderOf e ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hord
  have : Fact r.Prime := ⟨hr⟩
  have hpos : orderOf e ≠ 0 := (orderOf_pos e).ne'
  have hord' : orderOf (e ^ (orderOf e / r)) = r := orderOf_pow_orderOf_div hpos hrdvd
  have he'E : e ^ (orderOf e / r) ∈ E := E.pow_mem he _
  have hr2 : r ≠ 2 := by
    intro hr2
    have hodd := odd_orderOf_of_mem_pPrimeCoreOf (hEle he'E)
    rw [hord', hr2] at hodd
    exact absurd hodd (by decide)
  have he'Op : e ^ (orderOf e / r) ∈ Op r (Fm H) :=
    mem_Op_of_orderOf_prime (Fm_isNilpotent H) (hEF he'E) hord'
  have hfix' : t * e ^ (orderOf e / r) * t⁻¹ = e ^ (orderOf e / r) := by
    rw [← conj_pow, hte]
  have h1 := hfix r hr hr2 _ he'Op hfix'
  rw [h1, orderOf_one] at hord'
  exact hr.one_lt.ne hord'

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
