module

public import CFSG.CGT.PushingUpLit.A78Sp4.Data
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem mem_cj_iff (g : G) (H : Subgroup G) (x : G) : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  show x ∈ H.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mul_mem_cj (g : G) {H : Subgroup G} {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cj g H :=
  Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem mul_mem_cj_iff (g : G) (H : Subgroup G) (x : G) : g * x * g⁻¹ ∈ cj g H ↔ x ∈ H := by
  rw [mem_cj_iff]
  have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [this]

theorem cj_cj (a b : G) (H : Subgroup G) : cj a (cj b H) = cj (a * b) H := by
  ext x
  rw [mem_cj_iff, mem_cj_iff, mem_cj_iff]
  have : b⁻¹ * (a⁻¹ * x * a) * b = (a * b)⁻¹ * x * (a * b) := by group
  rw [this]

theorem cj_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : cj g H ≤ cj g K :=
  Subgroup.map_mono h

theorem card_cj (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cj_eq_self_of_mem {g : G} {H : Subgroup G} (hg : g ∈ H) : cj g H = H := by
  ext x
  rw [mem_cj_iff]
  exact ⟨fun hx => by simpa [mul_assoc] using H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg),
    fun hx => H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg⟩

theorem ElemAb2.mono {E F : Subgroup G} (hE : ElemAb2 E) (h : F ≤ E) : ElemAb2 F :=
  fun x hx y hy => hE x (h hx) y (h hy)

theorem ElemAb2.isPGroup {E : Subgroup G} (hE : ElemAb2 E) : IsPGroup 2 E := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have h := (hE x x.2 x x.2).2
  simpa [pow_two] using h

theorem elemAb2_cj {H : Subgroup G} (hH : ElemAb2 H) (g : G) : ElemAb2 (cj g H) := by
  intro x hx y hy
  rw [mem_cj_iff] at hx hy
  obtain ⟨h1, h2⟩ := hH _ hx _ hy
  refine ⟨?_, ?_⟩
  · calc x * y = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group
  · have h3 := (hH _ hx _ hx).2
    calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group

theorem isSylowOf_cj [Finite G] {P K : Subgroup G} (hP : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (cj g P) (cj g K) := by
  refine isSylowOf_of_card (cj_mono g hP.le) ?_
  rw [card_cj, card_cj]
  exact hP.card_eq

theorem isSylowOf_cj_of_mem [Finite G] {P K : Subgroup G} (hP : IsSylowOf 2 P K) {g : G}
    (hg : g ∈ K) : IsSylowOf 2 (cj g P) K := by
  have h := isSylowOf_cj hP g
  rwa [cj_eq_self_of_mem hg] at h

theorem exists_isSylowOf_ge [Finite G] {U K : Subgroup G} (hU : IsPGroup 2 U) (hUK : U ≤ K) :
    ∃ R : Subgroup G, IsSylowOf 2 R K ∧ U ≤ R := by
  have hU' : IsPGroup 2 (U.subgroupOf K) := hU.comap_subtype
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩,
    fun x hx => ⟨⟨x, hUK hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩⟩

theorem exists_eq_cj_of_isSylowOf [Finite G] {P P' K : Subgroup G} (hP : IsSylowOf 2 P K)
    (hP' : IsSylowOf 2 P' K) : ∃ k ∈ K, P' = cj k P := by
  obtain ⟨k, hk, hkc⟩ := hP.exists_mem_conj hP'
  exact ⟨k, hk, Subgroup.ext fun x => by rw [mem_cj_iff]; exact hkc x⟩

theorem exists_conj_le_of_isSylowOf [Finite G] {S K U : Subgroup G} (hS : IsSylowOf 2 S K)
    (hUK : U ≤ K) (hU : IsPGroup 2 U) : ∃ k ∈ K, cj k U ≤ S := by
  obtain ⟨R, hR, hUR⟩ := exists_isSylowOf_ge hU hUK
  obtain ⟨k, hk, hkc⟩ := exists_eq_cj_of_isSylowOf hS hR
  refine ⟨k⁻¹, K.inv_mem hk, fun x hx => ?_⟩
  rw [mem_cj_iff, inv_inv] at hx
  have h1 : k * x * k⁻¹ ∈ cj k S := hkc ▸ hUR hx
  rw [mem_cj_iff] at h1
  have h2 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rwa [h2] at h1

theorem cj_centralizer_singleton (w y : G) :
    cj w (Subgroup.centralizer ({y} : Set G)) = Subgroup.centralizer ({w * y * w⁻¹} : Set G) := by
  ext x
  rw [mem_cj_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (w * y * w⁻¹) = w * (w⁻¹ * x * w * y) * w⁻¹ := by group
      _ = w * (y * (w⁻¹ * x * w)) * w⁻¹ := by rw [h]
      _ = w * y * w⁻¹ * x := by group
  · intro h
    calc w⁻¹ * x * w * y = w⁻¹ * (x * (w * y * w⁻¹)) * w := by group
      _ = w⁻¹ * (w * y * w⁻¹ * x) * w := by rw [h]
      _ = y * (w⁻¹ * x * w) := by group

theorem exists_eq_cj_of_centralizer [Finite G] {a y w : G} (hw : w * y * w⁻¹ = a)
    {P R : Subgroup G} (hP : IsSylowOf 2 P (Subgroup.centralizer ({y} : Set G)))
    (hR : IsSylowOf 2 R (Subgroup.centralizer ({a} : Set G))) : ∃ h0 : G, R = cj h0 P := by
  have hP' := isSylowOf_cj hP w
  rw [cj_centralizer_singleton, hw] at hP'
  obtain ⟨k, -, hk⟩ := exists_eq_cj_of_isSylowOf hP' hR
  exact ⟨k * w, by rw [hk, cj_cj]⟩

theorem exists_fixed_conj_of_not_dvd {p : ℕ} [Fact p.Prime] [Finite G] {T : Subgroup G}
    (hT : IsPGroup p T) {X : Set G} (hX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hp : ¬ p ∣ Nat.card X) : ∃ x ∈ X, ∀ t ∈ T, t * x * t⁻¹ = x := by
  let _ : MulAction T X :=
    { smul := fun t x => ⟨(t : G) * x * (t : G)⁻¹, hX t t.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : T) : G) * x * ((1 : T) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : T) : G) * x * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹
        simp [mul_assoc]) }
  obtain ⟨x, hx⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card X hp
  exact ⟨x, x.2, fun t ht => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx ⟨t, ht⟩)⟩

theorem exists_fixed_conj_ne_of_dvd {p : ℕ} [Fact p.Prime] [Finite G] {T : Subgroup G}
    (hT : IsPGroup p T) {X : Set G} (hX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hp : p ∣ Nat.card X) {x₀ : G} (hx₀ : x₀ ∈ X) (hfix : ∀ t ∈ T, t * x₀ * t⁻¹ = x₀) :
    ∃ x ∈ X, x ≠ x₀ ∧ ∀ t ∈ T, t * x * t⁻¹ = x := by
  let _ : MulAction T X :=
    { smul := fun t x => ⟨(t : G) * x * (t : G)⁻¹, hX t t.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : T) : G) * x * ((1 : T) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : T) : G) * x * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹
        simp [mul_assoc]) }
  have hfx : (⟨x₀, hx₀⟩ : X) ∈ MulAction.fixedPoints T X :=
    MulAction.mem_fixedPoints.2 fun t => Subtype.ext (hfix t t.2)
  obtain ⟨b, hb, hab⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point X hp hfx
  exact ⟨b, b.2, fun h => hab (Subtype.ext h.symm),
    fun t ht => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hb ⟨t, ht⟩)⟩

theorem exists_fixed_ne_one [Finite G] {T Z : Subgroup G} (hT : IsPGroup 2 T) (hZ : ElemAb2 Z)
    (hZ1 : Z ≠ ⊥) (hTZ : ∀ t ∈ T, cj t Z = Z) :
    ∃ z ∈ Z, z ≠ 1 ∧ ∀ t ∈ T, t * z * t⁻¹ = z := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ.isPGroup
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hZ1 (Subgroup.card_eq_one.1 (by simpa using hn))
  have hX : ∀ t ∈ T, ∀ x ∈ (Z : Set G), t * x * t⁻¹ ∈ (Z : Set G) := by
    intro t ht x hx
    have h := mul_mem_cj t (H := Z) hx
    rwa [hTZ t ht] at h
  obtain ⟨z, hz, hz1, hzT⟩ := exists_fixed_conj_ne_of_dvd hT hX
    (by show 2 ∣ Nat.card Z; rw [hn]; exact dvd_pow_self 2 hn0)
    (Z.one_mem : (1 : G) ∈ (Z : Set G)) (fun t _ => by simp)
  exact ⟨z, hz, hz1, hzT⟩

theorem card_le_card_centralizer_sq [Finite G] {E : Subgroup G} (hE : ElemAb2 E) {a : G}
    (ha : a * a = 1) (haE : ∀ x ∈ E, a * x * a⁻¹ ∈ E) :
    Nat.card E ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) ^ 2 := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let φ : E →* E := MonoidHom.mk'
    (fun x => ⟨(x : G) * (a * x * a⁻¹), E.mul_mem x.2 (haE x x.2)⟩)
    (fun x y => by
      apply Subtype.ext
      have h1 := (hE _ y.2 _ (haE x x.2)).1
      show ((x * y : E) : G) * (a * ((x * y : E) : G) * a⁻¹) =
        ((x : G) * (a * x * a⁻¹)) * ((y : G) * (a * y * a⁻¹))
      rw [Subgroup.coe_mul]
      calc (x : G) * y * (a * (x * y) * a⁻¹)
          = x * (y * (a * x * a⁻¹)) * (a * y * a⁻¹) := by group
        _ = x * ((a * x * a⁻¹) * y) * (a * y * a⁻¹) := by rw [h1]
        _ = x * (a * x * a⁻¹) * (y * (a * y * a⁻¹)) := by group)
  have hker : ∀ x : E, φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxx : (x : G) * x = 1 := (hE x x.2 x x.2).2
    constructor
    · intro h
      have h' : (x : G) * (a * x * a⁻¹) = 1 := congrArg Subtype.val h
      have h2 : a * x * a⁻¹ = x := by
        rw [eq_inv_of_mul_eq_one_right h']
        exact inv_eq_of_mul_eq_one_right hxx
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h2]
        _ = a * x := by group
    · intro h
      apply Subtype.ext
      show (x : G) * (a * x * a⁻¹) = 1
      calc (x : G) * (a * x * a⁻¹) = (x * a) * x * a⁻¹ := by group
        _ = (a * x) * x * a⁻¹ := by rw [h]
        _ = a * (x * x) * a⁻¹ := by group
        _ = 1 := by rw [hxx]; group
  have hrange : ∀ x : E, ((φ x : E) : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := (hE _ x.2 _ (haE x x.2)).1
    show (x : G) * (a * x * a⁻¹) * a = a * ((x : G) * (a * x * a⁻¹))
    calc (x : G) * (a * x * a⁻¹) * a = (x : G) * a * x := by group
      _ = a * a * x * a⁻¹ * x := by rw [ha, hinv, one_mul]
      _ = a * ((a * x * a⁻¹) * x) := by group
      _ = a * (x * (a * x * a⁻¹)) := by rw [h1]
  have hK : Nat.card φ.ker ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have hle : φ.ker.map E.subtype ≤ E ⊓ Subgroup.centralizer ({a} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, (hker x).1 hx⟩
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    exact Subgroup.card_le_of_le hle
  have hR : Nat.card φ.range ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have hle : φ.range.map E.subtype ≤ E ⊓ Subgroup.centralizer ({a} : Set G) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨(φ x).2, hrange x⟩
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    exact Subgroup.card_le_of_le hle
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hcard
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) *
        Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.mul_le_mul hK hR
    _ = _ := (sq _).symm

theorem mem_of_commute_involution [Finite G] {V : Subgroup G} {m : ℕ} (hV : ElemAb2 V)
    (hVcard : Nat.card V = m) (hrank : ∀ E : Subgroup G, ElemAb2 E → Nat.card E ≤ m)
    {a : G} (ha : a * a = 1) (hcomm : ∀ v ∈ V, a * v = v * a) : a ∈ V := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hmul : ∀ v ∈ V, ∀ w ∈ V, v * a * (w * a) = v * w := by
    intro v _ w hw
    calc v * a * (w * a) = v * (a * w) * a := by group
      _ = v * (w * a) * a := by rw [hcomm w hw]
      _ = v * w * (a * a) := by group
      _ = v * w := by rw [ha, mul_one]
  have hmulR : ∀ v ∈ V, ∀ y ∈ V, v * a * y = v * y * a := by
    intro v _ y hy
    rw [mul_assoc, hcomm y hy, ← mul_assoc]
  let W : Subgroup G :=
    { carrier := {x | x ∈ V ∨ ∃ v ∈ V, x = v * a}
      mul_mem' := by
        rintro x y (hx | ⟨v, hv, rfl⟩) (hy | ⟨w, hw, rfl⟩)
        · exact Or.inl (V.mul_mem hx hy)
        · exact Or.inr ⟨x * w, V.mul_mem hx hw, by rw [mul_assoc]⟩
        · exact Or.inr ⟨v * y, V.mul_mem hv hy, hmulR v hv y hy⟩
        · exact Or.inl (by rw [hmul v hv w hw]; exact V.mul_mem hv hw)
      one_mem' := Or.inl V.one_mem
      inv_mem' := by
        rintro x (hx | ⟨v, hv, rfl⟩)
        · exact Or.inl (V.inv_mem hx)
        · refine Or.inr ⟨v⁻¹, V.inv_mem hv, ?_⟩
          rw [mul_inv_rev, hinv]
          exact hcomm v⁻¹ (V.inv_mem hv) }
  have hW : ElemAb2 W := by
    rintro x (hx | ⟨v, hv, rfl⟩) y (hy | ⟨w, hw, rfl⟩)
    · exact hV x hx y hy
    · refine ⟨?_, (hV x hx x hx).2⟩
      calc x * (w * a) = x * w * a := (mul_assoc _ _ _).symm
        _ = w * x * a := by rw [(hV x hx w hw).1]
        _ = w * a * x := (hmulR w hw x hx).symm
    · refine ⟨?_, by rw [hmul v hv v hv]; exact (hV v hv v hv).2⟩
      calc v * a * y = v * y * a := hmulR v hv y hy
        _ = y * v * a := by rw [(hV v hv y hy).1]
        _ = y * (v * a) := mul_assoc _ _ _
    · refine ⟨?_, by rw [hmul v hv v hv]; exact (hV v hv v hv).2⟩
      rw [hmul v hv w hw, hmul w hw v hv]
      exact (hV v hv w hw).1
  have hle : V ≤ W := fun x hx => Or.inl hx
  have hcard : Nat.card W ≤ Nat.card V := hVcard ▸ hrank W hW
  have hEq : V = W := Subgroup.eq_of_le_of_card_ge hle hcard
  have haW : a ∈ W := Or.inr ⟨1, V.one_mem, by simp⟩
  rwa [← hEq] at haW

theorem inf_ne_bot_of_quot_cyclic [Finite G] {S J C : Subgroup G} (hJ : (J.subgroupOf S).Normal)
    (hcyc : ∃ s ∈ S, ∀ x ∈ S, ∃ k : ℤ, (s ^ k)⁻¹ * x ∈ J) (hCS : C ≤ S) (hC : ElemAb2 C)
    (h4 : 4 ≤ Nat.card C) : ∃ y ∈ C, y ∈ J ∧ y ≠ 1 := by
  obtain ⟨s, hs, hall⟩ := hcyc
  have hcycQ : IsCyclic (S ⧸ J.subgroupOf S) := by
    refine ⟨QuotientGroup.mk ⟨s, hs⟩, fun q => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hall x x.2
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hk
  let φ : C →* S ⧸ J.subgroupOf S :=
    (QuotientGroup.mk' (J.subgroupOf S)).comp (Subgroup.inclusion hCS)
  have hker : ∀ x : C, φ x = 1 ↔ (x : G) ∈ J := by
    intro x
    show QuotientGroup.mk (Subgroup.inclusion hCS x) = (1 : S ⧸ J.subgroupOf S) ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hrange : Nat.card φ.range ≤ 2 := by
    have := hcycQ
    have hexp : Monoid.exponent φ.range ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, ⟨x, rfl⟩⟩
      apply Subtype.ext
      show (φ x) ^ 2 = 1
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using (hC x x.2 x x.2).2)
      rw [this, map_one]
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  have hcard := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hcard
  by_contra hcon
  push Not at hcon
  have hker1 : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).2 (Subtype.ext (hcon x x.2 ((hker x).1 hx)))
  rw [hker1, Subgroup.card_bot, one_mul] at hcard
  omega

end CFSG.CGT.PushingUpLit.A78Sp4
