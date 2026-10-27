module

public import CFSG.LocalAnalysis.GLTheoremA.S8.A9Lemma
public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12
public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.HNRows

open Equiv Equiv.Perm
open scoped Pointwise commutatorElement


theorem comm_of_fix' {n k : ℕ} {σ a : Perm (Fin n)} (hσ : ∀ i : Fin n, i.val < k → σ i = i)
    (ha1 : ∀ i : Fin n, k ≤ i.val → a i = i) (ha2 : ∀ i : Fin n, i.val < k → (a i).val < k) :
    σ * a = a * σ := by
  ext i
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hi : i.val < k
  · rw [hσ _ (ha2 i hi), hσ i hi]
  · have h2 : k ≤ (σ i).val := by
      by_contra hc
      have e := hσ (σ i) (by omega)
      exact hi (by rw [← σ.injective e]; omega)
    rw [ha1 i (by omega), ha1 _ h2]

@[expose] def c3A : alternatingGroup (Fin 8) :=
  ⟨swap 0 2 * swap 0 1, by
    rw [Equiv.Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]; rfl⟩

theorem orderOf_c3A : orderOf c3A = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext (by unfold c3A; decide)) ?_
  intro h
  have := congrArg (fun σ : alternatingGroup (Fin 8) => (σ : Perm (Fin 8)) 0) h
  revert this
  unfold c3A
  decide

@[expose] def fix3 : Subgroup (alternatingGroup (Fin 8)) :=
  (fixingSubgroup (Perm (Fin 8)) {i : Fin 8 | i.val < 3}).comap
    (alternatingGroup (Fin 8)).subtype

theorem mem_fix3 (σ : alternatingGroup (Fin 8)) :
    σ ∈ fix3 ↔ ∀ i : Fin 8, i.val < 3 → (σ : Perm (Fin 8)) i = i := by
  rw [fix3, Subgroup.mem_comap, mem_fixingSubgroup_iff]
  exact ⟨fun h i hi => h i hi, fun h i hi => h i hi⟩

theorem fix3_comm {σ : alternatingGroup (Fin 8)} (hσ : σ ∈ fix3) : σ * c3A = c3A * σ := by
  refine Subtype.ext (comm_of_fix' ((mem_fix3 σ).1 hσ) ?_ ?_)
  · unfold c3A; decide
  · unfold c3A; decide

@[expose] def shift3' : Fin 5 ≃ {i : Fin 8 // 3 ≤ i.val} where
  toFun j := ⟨⟨j.val + 3, by omega⟩, by simp⟩
  invFun i := ⟨i.1.val - 3, by have := i.1.isLt; omega⟩
  left_inv j := by ext; simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := i.2
    simp only
    omega

abbrev ext3' : Perm (Fin 5) →* Perm (Fin 8) := extendDomainHom shift3'

theorem ext3'_fix (τ : Perm (Fin 5)) {i : Fin 8} (hi : i.val < 3) : ext3' τ i = i := by
  rw [extendDomainHom_apply]
  exact extendDomain_apply_not_subtype τ shift3' (by omega)

theorem ext3'_mem (τ : alternatingGroup (Fin 5)) : ext3' τ ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, extendDomainHom_apply, sign_extendDomain]
  exact τ.2

@[expose] def alt5Hom : alternatingGroup (Fin 5) →* fix3 where
  toFun τ := ⟨⟨ext3' τ, ext3'_mem τ⟩, (mem_fix3 _).2 fun _ hi => ext3'_fix τ hi⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem alt5Hom_injective : Function.Injective alt5Hom := fun _ _ h =>
  Subtype.ext (extendDomainHom_injective shift3' (congrArg (fun x : fix3 =>
    ((x : alternatingGroup (Fin 8)) : Perm (Fin 8))) h))

theorem alt5Hom_surjective : Function.Surjective alt5Hom := by
  rintro ⟨⟨σ, hσ⟩, hfix⟩
  have hfix' := (mem_fix3 _).1 hfix
  have hge : ∀ i : Fin 8, 3 ≤ i.val → 3 ≤ (σ i).val := by
    intro i hi
    by_contra h
    have e := hfix' (σ i) (by omega)
    exact absurd (σ.injective e) (by intro h'; rw [h'] at h; omega)
  have hge' : ∀ i : Fin 8, 3 ≤ i.val → 3 ≤ (σ⁻¹ i).val := by
    intro i hi
    by_contra h
    have e := hfix' (σ⁻¹ i) (by omega)
    rw [Perm.coe_inv, Equiv.apply_symm_apply] at e
    rw [Perm.coe_inv, ← e] at h
    omega
  let τ : Perm (Fin 5) :=
    { toFun := fun j => shift3'.symm ⟨σ (shift3' j), hge _ (shift3' j).2⟩
      invFun := fun j => shift3'.symm ⟨σ⁻¹ (shift3' j), hge' _ (shift3' j).2⟩
      left_inv := fun j => by simp
      right_inv := fun j => by simp }
  have hτ : ext3' τ = σ := by
    ext i
    by_cases hi : 3 ≤ i.val
    · rw [extendDomainHom_apply]
      have := extendDomain_apply_subtype τ shift3' (b := i) hi
      rw [this]
      simp [τ]
    · rw [ext3'_fix τ (by omega), hfix' i (by omega)]
  refine ⟨⟨τ, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup, ← sign_extendDomain τ shift3', ← extendDomainHom_apply, hτ]
    exact hσ
  · apply Subtype.ext
    apply Subtype.ext
    exact hτ

@[expose] noncomputable def alt5Equiv : alternatingGroup (Fin 5) ≃* fix3 :=
  MulEquiv.ofBijective alt5Hom ⟨alt5Hom_injective, alt5Hom_surjective⟩

theorem fix3_simple : IsSimpleGroup fix3 := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact MulEquiv.isSimpleGroup alt5Equiv.symm

theorem card_fix3 : Nat.card fix3 = 60 := by
  rw [← Nat.card_congr alt5Equiv.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide


section Generic

variable {Y : Type} [Group Y] [Finite Y]


theorem mem_normalizer_of_conj_le {Q : Type*} [Group Q] [Finite Q] {T : Subgroup Q} {g : Q}
    (h : ∀ x ∈ T, g * x * g⁻¹ ∈ T) : g ∈ Subgroup.normalizer (T : Set Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]



theorem card_sup_of_inf_bot {H T : Subgroup Y} (hN : H ≤ Subgroup.normalizer (T : Set Y))
    (hb : H ⊓ T = ⊥) : Nat.card ↥(H ⊔ T) = Nat.card H * Nat.card T := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H T hN
  let f : H × T → ↥(H ⊔ T) := fun p => ⟨p.1 * p.2, by
    have : (p.1 : Y) * p.2 ∈ ((H ⊔ T : Subgroup Y) : Set Y) := by
      rw [hset]; exact Set.mul_mem_mul p.1.2 p.2.2
    exact this⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h1, t1⟩ ⟨h2, t2⟩ heq
      have e : (h1 : Y) * t1 = h2 * t2 := congrArg Subtype.val heq
      have hm : (h2 : Y)⁻¹ * h1 = t2 * (t1 : Y)⁻¹ := by
        calc (h2 : Y)⁻¹ * h1 = (h2 : Y)⁻¹ * (h1 * t1) * (t1 : Y)⁻¹ := by group
          _ = (h2 : Y)⁻¹ * (h2 * t2) * (t1 : Y)⁻¹ := by rw [e]
          _ = t2 * (t1 : Y)⁻¹ := by group
      have hmem : (h2 : Y)⁻¹ * h1 ∈ H ⊓ T :=
        ⟨H.mul_mem (H.inv_mem h2.2) h1.2, hm ▸ T.mul_mem t2.2 (T.inv_mem t1.2)⟩
      rw [hb, Subgroup.mem_bot] at hmem
      have hh : (h1 : Y) = h2 := by
        have := mul_inv_cancel_left (h2 : Y) h1
        rw [hmem, mul_one] at this
        exact this.symm
      have ht : (t1 : Y) = t2 := by rw [hh] at e; exact mul_left_cancel e
      rw [Subtype.ext hh, Subtype.ext ht]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (H : Set Y) * (T : Set Y) := by rw [← hset]; exact hx
      obtain ⟨a, ha, b, hb', rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb'⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem le_of_simple {S K : Subgroup Y} (hS : IsSimpleGroup S)
    (hKn : ∀ g ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ K) {x : Y} (hxS : x ∈ S) (hxK : x ∈ K) (hx1 : x ≠ 1) :
    S ≤ K := by
  have hN : (K.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hKn g g.2 n hn⟩
  haveI := hS
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf S) with h | h
  · exfalso
    have : (⟨x, hxS⟩ : S) ∈ K.subgroupOf S := Subgroup.mem_subgroupOf.2 hxK
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (congrArg Subtype.val this)
  · intro s hs
    have : (⟨s, hs⟩ : S) ∈ K.subgroupOf S := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.1 this

theorem centralizer_conj (g x : Y) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set Y) =
      (Subgroup.centralizer ({x} : Set Y)).map (MulAut.conj g).toMonoidHom := by
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * c * g, ?_, by simp [MulAut.conj_apply]; group⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have : g * (g⁻¹ * c * g * x) * g⁻¹ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by
      calc g * (g⁻¹ * c * g * x) * g⁻¹ = c * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * c := h
        _ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by group
    simpa using this
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hu
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * u * g⁻¹ * (g * x * g⁻¹) = g * (u * x) * g⁻¹ := by group
      _ = g * (x * u) * g⁻¹ := by rw [hu]
      _ = g * x * g⁻¹ * (g * u * g⁻¹) := by group




theorem conj_mem_centralizer {T : Subgroup Y} {g k : Y} (hg : g ∈ Subgroup.normalizer (T : Set Y))
    (hk : k ∈ Subgroup.centralizer (T : Set Y)) :
    g * k * g⁻¹ ∈ Subgroup.centralizer (T : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) r).1 hr
  have h := hk _ hr'
  calc r * (g * k * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = g * k * g⁻¹ * r := by group

theorem commutator_eq_self_of_simple {H : Subgroup Y} (hS : IsSimpleGroup H)
    (hnab : ∃ a b : H, a * b ≠ b * a) : ⁅H, H⁆ = H := by
  have hle : ⁅H, H⁆ ≤ H := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  refine le_antisymm hle ?_
  obtain ⟨a, b, hab⟩ := hnab
  have hx1 : ⁅(a : Y), (b : Y)⁆ ≠ 1 := by
    intro h
    apply hab
    apply Subtype.ext
    simpa [commutatorElement_eq_one_iff_mul_comm] using h
  refine le_of_simple hS (fun g hg k hk => ?_) (H.mul_mem (H.mul_mem (H.mul_mem a.2 b.2)
    (H.inv_mem a.2)) (H.inv_mem b.2)) (Subgroup.commutator_mem_commutator a.2 b.2) hx1
  have hkH : k ∈ H := hle hk
  have : g * k * g⁻¹ = ⁅g, k⁆ * k := by rw [commutatorElement_def]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hg hkH) hk

theorem eq_one_of_two_elem {d z l : Y} {L' : Subgroup Y} (hd3 : d ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers d) (hl : l ∈ L') (hzl : z * l = l * z)
    (hinf : Subgroup.zpowers d ⊓ L' = ⊥) {k : ℕ} (ht : (z * l) ^ (2 ^ k) = 1) : z = 1 := by
  have h1 : z ^ (2 ^ k) * l ^ (2 ^ k) = 1 := by rw [← (Commute.mul_pow hzl _)]; exact ht
  have h2 : z ^ (2 ^ k) = (l ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hmem : z ^ (2 ^ k) ∈ Subgroup.zpowers d ⊓ L' :=
    ⟨Subgroup.pow_mem _ hz _, h2 ▸ L'.inv_mem (L'.pow_mem hl _)⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hd1 := orderOf_dvd_of_pow_eq_one hz3
  have hd2 := orderOf_dvd_of_pow_eq_one hmem
  have hco : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have : orderOf z ∣ 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rwa [hco.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem three_le_card {T : Subgroup Y} {t u : Y} (ht : t ∈ T) (hu : u ∈ T) (ht1 : t ≠ 1)
    (hu1 : u ≠ 1) (htu : u ≠ t) : 3 ≤ Nat.card T := by
  classical
  let f : Fin 3 → T := ![1, ⟨t, ht⟩, ⟨u, hu⟩]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  simpa using this




theorem i2014_core (hc : A9.A9Fact) {s₁ s₃ : Y} {L : Subgroup Y}
    {ψ : alternatingGroup (Fin 9) →* Y} (hψ : Function.Injective ψ) (hψr : ψ.range = L)
    (hcls : ∀ d : Y, orderOf d = 3 → IsConj s₁ d ∨ IsConj s₃ d)
    (hc3 : Nat.card (Subgroup.centralizer ({s₃} : Set Y)) = 29160)
    (hC1 : Subgroup.centralizer ({s₁} : Set Y) = Subgroup.zpowers s₁ ⊔ L)
    (hinf : Subgroup.zpowers s₁ ⊓ L = ⊥) (hLs : ∀ l ∈ L, l * s₁ = s₁ * l)
    (hcom : ⁅Subgroup.centralizer ({s₁} : Set Y), Subgroup.centralizer ({s₁} : Set Y)⁆ = L)
    (hs1 : orderOf s₁ = 3)
    {I R : Subgroup Y} (hIL : I ≤ L) (eI : I ≃* alternatingGroup (Fin 8)) (hR : IsPGroup 2 R)
    (hIR : I ≤ Subgroup.normalizer (R : Set Y)) (hsR : s₁ ∈ Subgroup.normalizer (R : Set Y)) :
    I ≤ Subgroup.centralizer (R : Set Y) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hIs : IsSimpleGroup I := eI.isSimpleGroup_congr.2 (alternatingGroup.isSimpleGroup (by simp))
  set y : Y := ((eI.symm c3A : I) : Y) with hy
  set H : Subgroup Y := (fix3.map eI.symm.toMonoidHom).map I.subtype with hHdef
  have hHI : H ≤ I := Subgroup.map_subtype_le _
  have eH : H ≃* fix3 :=
    ((fix3.map eI.symm.toMonoidHom).equivMapOfInjective I.subtype I.subtype_injective).symm.trans
      (fix3.equivMapOfInjective _ eI.symm.injective).symm
  have hHs : IsSimpleGroup H := eH.isSimpleGroup_congr.2 fix3_simple
  have hHc : Nat.card H = 60 := by rw [Nat.card_congr eH.toEquiv, card_fix3]
  have hyI : y ∈ I := (eI.symm c3A).2
  have hyo : orderOf y = 3 := by
    rw [hy, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_c3A]
  have hHy : ∀ h ∈ H, h * y = y * h := by
    rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    have := congrArg (fun z : alternatingGroup (Fin 8) => ((eI.symm z : I) : Y)) (fix3_comm hσ)
    simp only [map_mul, Subgroup.coe_mul] at this
    exact this
  have hIs1 : ∀ x ∈ I, x * s₁ = s₁ * x := fun x hx => hLs x (hIL hx)
  have hs13 : s₁ ^ 3 = 1 := by rw [← hs1]; exact pow_orderOf_eq_one s₁
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hyo; norm_num at hyo
  have hna : s₁ ∉ Subgroup.zpowers y := by
    intro hs
    have hsL : s₁ ∈ L := hIL (Subgroup.zpowers_le.2 hyI hs)
    have : s₁ ∈ Subgroup.zpowers s₁ ⊓ L := ⟨Subgroup.mem_zpowers _, hsL⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hs1
    norm_num at hs1
  obtain ⟨hDel, hDc⟩ := CFSG.LocalAnalysis.GLTheoremA.Prop53.isElemAbelian_card_sup_zpowers hp3
    (hIs1 y hyI).symm hs13 hy3 hy1 hna
  set D : Subgroup Y := Subgroup.zpowers s₁ ⊔ Subgroup.zpowers y with hD
  have hDN : D ≤ Subgroup.normalizer (R : Set Y) :=
    sup_le (Subgroup.zpowers_le.2 hsR) (Subgroup.zpowers_le.2 (hIR hyI))
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp3 Nat.prime_two).1 (hp3.dvd_of_dvd_pow h)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    hp3 D R (fun m => Subtype.ext (by simpa using hDel.2 _ m.2)) hDc hR3 hDN
  suffices hH : H ≤ Subgroup.centralizer (R : Set Y) by
    obtain ⟨x, hxH, hx1⟩ : ∃ x ∈ H, x ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).2 hcon
      rw [this, Subgroup.card_bot] at hHc
      norm_num at hHc
    have hle := le_of_simple hIs (K := I ⊓ Subgroup.centralizer (R : Set Y))
      (fun g hg k hk => ⟨I.mul_mem (I.mul_mem hg hk.1) (I.inv_mem hg),
        conj_mem_centralizer (hIR hg) hk.2⟩) (hHI hxH) ⟨hHI hxH, hH hxH⟩ hx1
    exact hle.trans inf_le_right
  rw [Subgroup.le_centralizer_iff, hgen]
  refine iSup₂_le fun d hd1 => ?_
  set dd : Y := (d : Y) with hdd
  have hdd1 : dd ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdd3 : orderOf dd = 3 := orderOf_eq_prime (hDel.2 _ d.2) hdd1
  have hHd : ∀ h ∈ H, h * dd = dd * h := by
    intro h hh
    have hDc' : D ≤ Subgroup.centralizer ({h} : Set Y) := sup_le
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hIs1 h (hHI hh)).symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hHy h hh).symm))
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hDc' d.2)).symm
  set T : Subgroup Y := R ⊓ Subgroup.centralizer ({dd} : Set Y) with hT
  have hT2 : IsPGroup 2 T := hR.to_le inf_le_left
  have hHT : H ≤ Subgroup.normalizer (T : Set Y) := by
    intro h hh
    refine mem_normalizer_of_conj_le fun x hx => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hIR (hHI hh)) x).1 hx.1
    · show h * x * h⁻¹ ∈ Subgroup.centralizer ({dd} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxd := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      have hhd := hHd h hh
      have hhd' : h⁻¹ * dd = dd * h⁻¹ := by
        calc h⁻¹ * dd = h⁻¹ * (dd * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * dd) * h⁻¹ := by rw [hhd]
          _ = dd * h⁻¹ := by group
      calc h * x * h⁻¹ * dd = h * x * (h⁻¹ * dd) := by group
        _ = h * x * (dd * h⁻¹) := by rw [hhd']
        _ = h * (x * dd) * h⁻¹ := by group
        _ = h * (dd * x) * h⁻¹ := by rw [hxd]
        _ = (h * dd) * x * h⁻¹ := by group
        _ = dd * h * x * h⁻¹ := by rw [hhd]
        _ = dd * (h * x * h⁻¹) := by group
  have hHCd : H ≤ Subgroup.centralizer ({dd} : Set Y) := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.2 (hHd h hh)
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  by_contra hTH
  rcases hcls dd hdd3 with h3A | h3B
  ·
    obtain ⟨g, hg⟩ := isConj_iff.1 h3A
    set c : Y →* Y := (MulAut.conj g).toMonoidHom with hcdef
    have hcinj : Function.Injective c := (MulAut.conj g).injective
    set L' : Subgroup Y := L.map c with hL'
    have hcs : c s₁ = dd := by rw [← hg]; rfl
    have hCd : Subgroup.centralizer ({dd} : Set Y) = Subgroup.zpowers dd ⊔ L' := by
      rw [← hg, centralizer_conj, hC1, Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    have hinf' : Subgroup.zpowers dd ⊓ L' = ⊥ := by
      rw [← hcs, ← MonoidHom.map_zpowers, ← Subgroup.map_inf _ _ _ hcinj, hinf, Subgroup.map_bot]
    have hLd : ∀ l ∈ L', l * dd = dd * l := by
      rintro _ ⟨l, hl, rfl⟩
      rw [← hcs, ← map_mul, ← map_mul, hLs l hl]
    have hcomd : ⁅Subgroup.centralizer ({dd} : Set Y), Subgroup.centralizer ({dd} : Set Y)⁆ = L' := by
      rw [← hg, centralizer_conj, ← Subgroup.map_commutator, hcom]
    have hnab : ∃ a b : H, a * b ≠ b * a :=
      CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hHc]; norm_num)
    have hHL' : H ≤ L' := by
      rw [← commutator_eq_self_of_simple hHs hnab, ← hcomd]
      exact Subgroup.commutator_mono hHCd hHCd
    have hdN : Subgroup.zpowers dd ≤ Subgroup.normalizer (L' : Set Y) :=
      Subgroup.zpowers_le.2 (mem_normalizer_of_conj_le fun l hl => by
        rw [← hLd l hl, mul_inv_cancel_right]; exact hl)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdN
    have hTL' : T ≤ L' := by
      intro t ht
      have ht' : t ∈ ((Subgroup.zpowers dd ⊔ L' : Subgroup Y) : Set Y) := by
        rw [← hCd]; exact ht.2
      rw [hset] at ht'
      obtain ⟨z, hz, l, hl, rfl⟩ := ht'
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hT2) ⟨_, ht⟩
      rw [Subgroup.orderOf_mk] at hm
      have hzl : z * l = l * z := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        exact ((Commute.zpow_left (hLd l hl).symm i)).eq
      have hz1 : z = 1 := eq_one_of_two_elem (hDel.2 _ d.2) hz hl hzl hinf'
        (by rw [← hm]; exact pow_orderOf_eq_one _)
      show z * l ∈ L'
      rw [hz1, one_mul]
      exact hl
    set ψ' : alternatingGroup (Fin 9) →* Y := c.comp ψ with hψ'
    have hψ'i : Function.Injective ψ' := hcinj.comp hψ
    have hψ'r : ψ'.range = L' := by rw [hψ', MonoidHom.range_comp, hψr]
    have h5 : ∀ f ∈ H, orderOf f = 5 → ∀ t ∈ T, f * t = t * f := by
      intro f hf hf5 t ht
      obtain ⟨f₉, hf₉⟩ : f ∈ ψ'.range := by rw [hψ'r]; exact hHL' hf
      set T₉ : Subgroup (alternatingGroup (Fin 9)) := T.comap ψ'
      set T' : Subgroup (Perm (Fin 9)) := T₉.map (alternatingGroup (Fin 9)).subtype
      have hfo : orderOf (f₉ : Perm (Fin 9)) = 5 := by
        rw [Subgroup.orderOf_coe, ← orderOf_injective ψ' hψ'i, hf₉, hf5]
      have hT'p : IsPGroup 2 T' := (hT2.comap_of_injective ψ' hψ'i).map _
      have hfN : (f₉ : Perm (Fin 9)) ∈ Subgroup.normalizer (T' : Set (Perm (Fin 9))) := by
        refine mem_normalizer_of_conj_le fun x hx => ?_
        obtain ⟨u, hu, rfl⟩ := hx
        refine ⟨f₉ * u * f₉⁻¹, ?_, by simp⟩
        show ψ' (f₉ * u * f₉⁻¹) ∈ T
        rw [map_mul, map_mul, map_inv, hf₉]
        exact (Subgroup.mem_normalizer_iff.1 (hHT hf) _).1 hu
      have key := A9.a9_lemma hc hfo (Subgroup.map_subtype_le _) hT'p hfN
      obtain ⟨u, hu⟩ : t ∈ ψ'.range := by rw [hψ'r]; exact hTL' ht
      have hu' : u ∈ T₉ := by show ψ' u ∈ T; rw [hu]; exact ht
      have h1 := key _ ⟨u, hu', rfl⟩
      have h2 : f₉ * u = u * f₉ := Subtype.ext h1
      rw [← hf₉, ← hu, ← map_mul, ← map_mul, h2]
    obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 (by rw [hHc]; norm_num)
    have hx1 : (x : Y) ≠ 1 := by
      intro h
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hx5
      norm_num at hx5
    have hle := le_of_simple hHs (K := H ⊓ Subgroup.centralizer (T : Set Y))
      (fun g hg k hk => ⟨H.mul_mem (H.mul_mem hg hk.1) (H.inv_mem hg),
        conj_mem_centralizer (hHT hg) hk.2⟩) x.2
      ⟨x.2, Subgroup.mem_centralizer_iff.2 fun t ht =>
        (h5 x x.2 (by rw [← Subgroup.orderOf_coe] at hx5; exact hx5) t ht).symm⟩ hx1
    exact hTH (Subgroup.le_centralizer_iff.1 (hle.trans inf_le_right))
  ·
    obtain ⟨g, hg⟩ := isConj_iff.1 h3B
    have hCd : Nat.card (Subgroup.centralizer ({dd} : Set Y)) = 29160 := by
      rw [← hg, centralizer_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective, hc3]
    have hHT0 : H ⊓ T = ⊥ := by
      by_contra hne
      obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
      have hle := le_of_simple hHs (K := H ⊓ T)
        (fun g hg k hk => ⟨H.mul_mem (H.mul_mem hg hk.1) (H.inv_mem hg),
          (Subgroup.mem_normalizer_iff.1 (hHT hg) k).1 hk.2⟩) hx.1 hx (fun h => hx1 (Subtype.ext h))
      have hdvd : Nat.card H ∣ Nat.card T :=
        Subgroup.card_dvd_of_le (hle.trans inf_le_right)
      rw [hHc, hk] at hdvd
      have : 3 ∣ 2 ^ k := (by norm_num : (3 : ℕ) ∣ 60).trans hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp3 Nat.prime_two).1 (hp3.dvd_of_dvd_pow this)
      omega
    have hcard := card_sup_of_inf_bot hHT hHT0
    have hle : H ⊔ T ≤ Subgroup.centralizer ({dd} : Set Y) := sup_le hHCd inf_le_right
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcard, hCd, hHc, hk] at hdvd
    have hk1 : k ≤ 1 := by
      by_contra h2
      have h4 : 4 ∣ 2 ^ k := (Nat.pow_dvd_pow 2 (show 2 ≤ k by omega))
      have : 60 * 4 ∣ 29160 := (Nat.mul_dvd_mul_left 60 h4).trans hdvd
      norm_num at this
    apply hTH
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    by_contra hne
    have hu : h * t * h⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hHT hh) t).1 ht
    have ht1 : t ≠ 1 := fun h1 => hne (by rw [h1, mul_one, one_mul])
    have hu1 : h * t * h⁻¹ ≠ 1 := fun h1 => ht1 (by
      have : t = h⁻¹ * (h * t * h⁻¹) * h := by group
      rw [this, h1]; group)
    have hut : h * t * h⁻¹ ≠ t := fun h1 => hne (by
      calc h * t = h * t * h⁻¹ * h := by group
        _ = t * h := by rw [h1])
    have h3 := three_le_card ht hu ht1 hu1 hut
    rw [hk] at h3
    have : 2 ^ k ≤ 2 := by
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    omega


end Generic

end CFSG.LocalAnalysis.GLTheoremA.S8.HNRows
