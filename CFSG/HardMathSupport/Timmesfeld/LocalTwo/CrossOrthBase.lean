module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Congr

variable {K K' : Type*} [Group K] [Group K']

theorem congr_conj_apply (e : K ≃* K') (x : K) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_mem_innerAut (e : K ≃* K') {y : MulAut K} (hy : y ∈ innerAut K) :
    MulAut.congr e y ∈ innerAut K' := by
  obtain ⟨k, rfl⟩ := hy
  exact ⟨e k, (congr_conj_apply e k).symm⟩

theorem conj_injective_of_mulEquiv (e : K ≃* K')
    (h : Function.Injective (MulAut.conj : K →* MulAut K)) :
    Function.Injective (MulAut.conj : K' →* MulAut K') := by
  intro a b hab
  have : MulAut.conj (e.symm a) = (MulAut.conj (e.symm b) : MulAut K) := by
    rw [← congr_conj_apply e.symm, ← congr_conj_apply e.symm, hab]
  exact e.symm.injective (h this)

theorem congr_symm_congr (e : K ≃* K') (x : MulAut K) :
    MulAut.congr e.symm (MulAut.congr e x) = x := by
  ext y
  simp [MulAut.congr_apply]

theorem congr_congr_symm (e : K ≃* K') (x : MulAut K') :
    MulAut.congr e (MulAut.congr e.symm x) = x := by
  ext y
  simp [MulAut.congr_apply]

theorem mem_fixSub_congr (e : K ≃* K') (x : MulAut K) (y : K') :
    y ∈ fixSub (MulAut.congr e x) ↔ e.symm y ∈ fixSub x := by
  rw [mem_fixSub, mem_fixSub]
  change e (x (e.symm y)) = y ↔ x (e.symm y) = e.symm y
  constructor
  · intro h
    simpa using congrArg e.symm h
  · intro h
    rw [h]; simp

theorem FieldCoreAt.congr {p : ℕ} {x : MulAut K} (h : FieldCoreAt p x) (e : K ≃* K') :
    FieldCoreAt p (MulAut.congr e x) := by
  obtain ⟨T, hTF, hTn, hTq, hTp, hfaith⟩ := h
  refine ⟨T.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [mem_fixSub_congr]
    simpa using hTF ht
  · rintro f hf _ ⟨t, ht, rfl⟩
    have hf0 : e.symm f ∈ fixSub x := (mem_fixSub_congr e x f).1 hf
    refine ⟨e.symm f * t * (e.symm f)⁻¹, hTn _ hf0 t ht, ?_⟩
    simp
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (T.equivMapOfInjective e.toMonoidHom e.injective) hTq
  · rwa [Subgroup.card_map_of_injective e.injective]
  · intro g hgp hgx hgT
    set g0 : MulAut K := (MulAut.congr e).symm g with hg0
    have hgg0 : MulAut.congr e g0 = g := (MulAut.congr e).apply_symm_apply g
    have h1 : orderOf g0 = orderOf g := MulEquiv.orderOf_eq (MulAut.congr e).symm g
    have h2 : g0 * x = x * g0 := by
      apply (MulAut.congr e).injective
      rw [map_mul, map_mul, hgg0]
      exact hgx
    have h3 : ∀ t ∈ T, g0 t = t := by
      intro t ht
      have := hgT (e t) ⟨t, ht, rfl⟩
      have h4 : (MulAut.congr e g0) (e t) = e (g0 t) := by
        simp [MulAut.congr_apply]
      rw [hgg0] at h4
      apply e.injective
      rw [← h4, this]
    have h5 := hfaith g0 (h1 ▸ hgp) h2 h3
    rw [← hgg0, h5, map_one]

end Congr

section Fixed

variable {P : Type*} [Group P]

theorem fieldCoreAt_of_normal_simple_fixed [Finite P] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) {δ : MulAut P}
    (hδp : orderOf δ = p) {N J : Subgroup P} (hN : ∀ t, δ t = t ↔ t ∈ N) (hJN : J ≤ N)
    (hJn : (J.subgroupOf N).Normal) (hJq : CFSG.IsQuasisimple J)
    (hquot : IsPGroup 2 (↥N ⧸ J.subgroupOf N))
    (hfix : fixingSubgroup (MulAut P) (J : Set P) = Subgroup.zpowers δ)
    {y : MulAut P} (hy : y ∈ innerAut P) (hy1 : y ≠ 1) (hyp : y ^ p = 1)
    (hcomm : y * δ = δ * y) : FieldCoreAt p δ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj
    (δ := δ) (x := δ) (h := 1) (by simp) hy hy1 hyp hcomm
  have hkN : k ∈ N := (hN k).1 hkδ
  have hkJ : k ∈ J := by
    set q : ↥N ⧸ J.subgroupOf N := (QuotientGroup.mk (⟨k, hkN⟩ : ↥N)) with hq
    have hqp : q ^ p = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have hkp : k ^ p = 1 := by rw [← hkord]; exact pow_orderOf_eq_one k
      have : (⟨k, hkN⟩ : ↥N) ^ p = 1 := Subtype.ext (by simpa using hkp)
      rw [this, QuotientGroup.mk_one]
    obtain ⟨m, hm⟩ := hquot q
    have h1 : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hqp
    have h2 : orderOf q ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime p (2 ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 : orderOf q = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hJp : ¬ Nat.Coprime p (Nat.card J) := by
    have hdvd : p ∣ Nat.card J := by
      have : orderOf (⟨k, hkJ⟩ : J) = p := by
        rw [Subgroup.orderOf_mk]
        exact hkord
      rw [← this]
      exact orderOf_dvd_natCard _
    exact fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hdvd
  refine ⟨J, fun j hj => (hN j).2 (hJN hj), fun f hf t ht => ?_, hJq, hJp, ?_⟩
  · have hfN : f ∈ N := (hN f).1 (mem_fixSub.1 hf)
    have hmem : (⟨t, hJN ht⟩ : ↥N) ∈ J.subgroupOf N := ht
    have := hJn.conj_mem _ hmem ⟨f, hfN⟩
    exact this
  · intro g hgp _ hgJ
    have hg : g ∈ fixingSubgroup (MulAut P) (J : Set P) :=
      (mem_fixingSubgroup_iff _).2 fun u hu => hgJ u hu
    rw [hfix] at hg
    have hdvd : orderOf g ∣ p := hδp ▸ orderOf_dvd_of_mem_zpowers hg
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

end Fixed

section Outer

@[expose] def OuterFields (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 2 → ¬ D ≤ innerAut K →
    ∃ x ∈ D, x ∉ innerAut K ∧ FieldCoreAt p x

variable {T P : Type*} [Group T] [Group P]

theorem map_innerAut_congr (e : T ≃* P) :
    (innerAut T).map (MulAut.congr e).toMonoidHom = innerAut P := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact congr_mem_innerAut e hy
  · intro hz
    refine ⟨MulAut.congr e.symm z, congr_mem_innerAut e.symm hz, ?_⟩
    exact congr_congr_symm e z

theorem isElemAbelian_map {p : ℕ} (φ : MulAut T ≃* MulAut P) {D : Subgroup (MulAut T)}
    (hD : IsElemAbelian p D) : IsElemAbelian p (D.map φ.toMonoidHom) :=
  CFSG.SectionRank.isElemAbelian_map hD _

theorem OuterFields.of_mulEquiv {p : ℕ} (e : T ≃* P) (h : OuterFields p P) : OuterFields p T := by
  intro D hD hc hDin
  set φ := MulAut.congr e with hφ
  have hD' : IsElemAbelian p (D.map φ.toMonoidHom) := isElemAbelian_map φ hD
  have hc' : Nat.card (D.map φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
  have hin' : ¬ D.map φ.toMonoidHom ≤ innerAut P := by
    intro hle
    apply hDin
    rw [← map_innerAut_congr e] at hle
    exact (Subgroup.map_le_map_iff_of_injective φ.injective).1 hle
  obtain ⟨x', ⟨x, hxD, rfl⟩, hx'in, hfc⟩ := h _ hD' hc' hin'
  refine ⟨x, hxD, fun hxin => hx'in (congr_mem_innerAut e hxin), ?_⟩
  have hfc' : FieldCoreAt p (MulAut.congr e x) := hfc
  have := FieldCoreAt.congr hfc' e.symm
  rwa [congr_symm_congr] at this

end Outer

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
