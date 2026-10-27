module

public import CFSG.Foundations.Basic

public section

namespace CFSG.CGT.Stroth77

open Subgroup

theorem exists_conj_eq_of_involutions {H : Type*} [Group H] [Finite H] {O : Subgroup H}
    (hO : Odd (Nat.card O)) {i j : H} (hi : i * i = 1) (hj : j * j = 1) (hij : i⁻¹ * j ∈ O) :
    ∃ c ∈ O, j = c⁻¹ * i * c := by
  set o := i⁻¹ * j with ho
  have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi
  have hj' : j = i * o := by rw [ho, ← mul_assoc, mul_inv_cancel, one_mul]
  have hinv : i * o * i⁻¹ = o⁻¹ := by
    rw [hj'] at hj
    have : i * o * i * o = 1 := by rw [← hj]; group
    rw [hii]
    calc i * o * i = i * o * i * o * o⁻¹ := by group
      _ = o⁻¹ := by rw [this, one_mul]
  have hodd : Odd (orderOf o) := by
    have h := Subgroup.orderOf_dvd_natCard O hij
    exact Odd.of_dvd_nat hO h
  set c := o ^ ((orderOf o + 1) / 2) with hc
  have hc2 : c * c = o := by
    rw [hc, ← pow_add]
    obtain ⟨k, hk⟩ := hodd
    have : (orderOf o + 1) / 2 + (orderOf o + 1) / 2 = orderOf o + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have hcinv : i * c * i⁻¹ = c⁻¹ := by
    rw [hc, ← conj_pow, hinv, inv_pow]
  refine ⟨c, O.pow_mem hij _, ?_⟩
  have h1 : c⁻¹ * i * c = c⁻¹ * (i * c * i⁻¹) * i := by group
  rw [h1, hcinv, ← mul_inv_rev, hc2]
  have h2 : o⁻¹ * i = i * o := by
    calc o⁻¹ * i = i * o * i⁻¹ * i := by rw [hinv]
      _ = i * o := by group
  rw [h2, hj']

theorem exists_normalizer_conj_of_unique {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {A : Subgroup G} (hAS : A ≤ S) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (Pr : Subgroup G → Prop) (hPrA : Pr A)
    (hPr : ∀ (B : Subgroup G) (g : G), Pr B → Pr (B.map (MulAut.conj g).toMonoidHom))
    (huniq : ∀ B : Subgroup G, B ≤ S → Pr B → B = A) {w a k : G} (hw : w ∈ A) (ha : a ∈ A)
    (hk : a = k⁻¹ * w * k) : ∃ n ∈ normalizer (A : Set G), a = n⁻¹ * w * n := by
  classical
  set C := centralizer ({a} : Set G) with hCdef
  have hAC : A ≤ C := fun x hx => by
    rw [hCdef, mem_centralizer_singleton_iff]; exact hAc x hx a ha
  set Ak := A.map (MulAut.conj k⁻¹).toMonoidHom with hAk
  have hAkC : Ak ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hCdef, mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hk]
    have := hAc w hw x hx
    calc k⁻¹ * x * k * (k⁻¹ * w * k) = k⁻¹ * (x * w) * k := by group
      _ = k⁻¹ * (w * x) * k := by rw [this]
      _ = k⁻¹ * w * k * (k⁻¹ * x * k) := by group
  have hAp : IsPGroup p A := S.2.to_le hAS
  have hAkp : IsPGroup p Ak := hAp.map _
  have hAp' : IsPGroup p (A.subgroupOf C) := hAp.comap_of_injective C.subtype Subtype.val_injective
  obtain ⟨P, hAP⟩ := hAp'.exists_le_sylow
  have hAkp' : IsPGroup p (Ak.subgroupOf C) :=
    hAkp.comap_of_injective C.subtype Subtype.val_injective
  obtain ⟨P', hAkP'⟩ := hAkp'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P' P
  have hPp : IsPGroup p ((P : Subgroup C).map C.subtype) := P.2.map _
  obtain ⟨Q, hPQ⟩ := hPp.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq G Q S
  have hAQ : A ≤ Q := fun x hx =>
    hPQ ⟨⟨x, hAC hx⟩, hAP (by rw [mem_subgroupOf]; exact hx), rfl⟩
  set B := Ak.map (MulAut.conj (c : G)).toMonoidHom with hB
  have hBQ : B ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    have hyC : y ∈ C := hAkC hy
    have h1 : (⟨y, hyC⟩ : C) ∈ (P' : Subgroup C) := hAkP' (by rw [mem_subgroupOf]; exact hy)
    have h3 : (c * ⟨y, hyC⟩ * c⁻¹ : C) ∈ ((c • P' : Sylow p C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, h1, by simp [MulAut.conj_apply]⟩
    rw [hc] at h3
    refine hPQ ⟨_, h3, ?_⟩
    simp [MulAut.conj_apply]
  have hconjS : ∀ X : Subgroup G, X ≤ Q → X.map (MulAut.conj m).toMonoidHom ≤ S := by
    intro X hX
    rintro _ ⟨x, hx, rfl⟩
    have : m * x * m⁻¹ ∈ ((m • Q : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨x, hX hx, by simp [MulAut.conj_apply]⟩
    rw [hm] at this
    simpa [MulAut.conj_apply] using this
  have hA1 : A.map (MulAut.conj m).toMonoidHom = A :=
    huniq _ (hconjS A hAQ) (hPr A m hPrA)
  have hPrB : Pr B := hPr _ _ (hPr A k⁻¹ hPrA)
  have hB1 : B.map (MulAut.conj m).toMonoidHom = A := huniq _ (hconjS B hBQ) (hPr B m hPrB)
  have hBA : B = A := by
    have e : ∀ X : Subgroup G,
        X = (X.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom := by
      intro X
      rw [Subgroup.map_map]
      ext x
      simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      constructor
      · intro hx; exact ⟨x, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩; convert hy using 1; group
    calc B = (B.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom := e B
      _ = A.map (MulAut.conj m⁻¹).toMonoidHom := by rw [hB1]
      _ = (A.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom := by rw [hA1]
      _ = A := (e A).symm
  set n := k * (c : G)⁻¹ with hn
  have hBx : ∀ y, y ∈ B ↔ n * y * n⁻¹ ∈ A := by
    intro y
    rw [hB, hAk, Subgroup.map_map]
    simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨z, hz, rfl⟩
      convert hz using 1
      rw [hn]; group
    · intro hy
      refine ⟨n * y * n⁻¹, hy, ?_⟩
      rw [hn]; group
  refine ⟨n, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    rw [← hBx x, hBA]
  · have hcC : (c : G) * a = a * c := mem_centralizer_singleton_iff.1 c.2
    calc a = (c : G) * a * (c : G)⁻¹ := by rw [hcC, mul_inv_cancel_right]
      _ = n⁻¹ * w * n := by rw [hk, hn]; group

theorem odd_natCard_oddCore_stroth (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore (G := X), ← CFSG.pPrimeCore_eq_piCore X 2]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem exists_lift_of_sylow {M H : Type*} [Group M] [Group H] [Finite H]
    (e : M ≃* H ⧸ CFSG.oddCore H) (T : Sylow 2 M) :
    ∃ l : ↥(T : Subgroup M) →* H, Function.Injective l ∧
      (∀ m, QuotientGroup.mk' (CFSG.oddCore H) (l m) = e m) ∧
      ∃ P : Sylow 2 H, (P : Subgroup H) = l.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.oddCore H)) :=
    QuotientGroup.mk'_surjective _
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ 2
    (Sylow.mapSurjective (f := (e : M →* H ⧸ CFSG.oddCore H)) e.surjective T)
  have hPmap : (P : Subgroup H).map (QuotientGroup.mk' (CFSG.oddCore H)) =
      (T : Subgroup M).map (e : M →* H ⧸ CFSG.oddCore H) := by
    have := congrArg (fun Q : Sylow 2 (H ⧸ CFSG.oddCore H) =>
      (Q : Subgroup (H ⧸ CFSG.oddCore H))) hP
    simpa [Sylow.coe_mapSurjective] using this
  have hcop : Nat.Coprime (Nat.card (P : Subgroup H)) (Nat.card (CFSG.oddCore H)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.2
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_natCard_oddCore_stroth H))
  have hinf : (P : Subgroup H) ⊓ CFSG.oddCore H = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.oddCore H)).comp (P : Subgroup H).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxO : (x : H) ∈ CFSG.oddCore H := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hx' : (x : H) ∈ (P : Subgroup H) ⊓ CFSG.oddCore H := ⟨x.2, hxO⟩
    rw [hinf, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  have hrange : (T : Subgroup M).map (e : M →* H ⧸ CFSG.oddCore H) =
      ((QuotientGroup.mk' (CFSG.oddCore H)).comp (P : Subgroup H).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
  let l : ↥(T : Subgroup M) →* H := (P : Subgroup H).subtype.comp
    ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
      ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp
        (e.subgroupMap (T : Subgroup M)).toMonoidHom))
  refine ⟨l, ?_, ?_, P, ?_⟩
  · intro m m' h
    have h1 := Subtype.ext h
    have h2 := (MonoidHom.ofInjective hinj).symm.injective h1
    have h3 := (MulEquiv.subgroupCongr hrange).injective h2
    exact (e.subgroupMap (T : Subgroup M)).injective h3
  · intro m
    have key : ((MonoidHom.ofInjective hinj ((MonoidHom.ofInjective hinj).symm
        (MulEquiv.subgroupCongr hrange ((e.subgroupMap (T : Subgroup M)) m))) : _) :
          H ⧸ CFSG.oddCore H) =
        ((QuotientGroup.mk' (CFSG.oddCore H)).comp (P : Subgroup H).subtype)
          ((MonoidHom.ofInjective hinj).symm
            (MulEquiv.subgroupCongr hrange ((e.subgroupMap (T : Subgroup M)) m))) :=
      MonoidHom.ofInjective_apply hinj
    rw [MulEquiv.apply_symm_apply] at key
    exact key.symm
  · apply le_antisymm
    · intro x hx
      obtain ⟨m, hm⟩ : ∃ m, (MonoidHom.ofInjective hinj).symm
          (MulEquiv.subgroupCongr hrange ((e.subgroupMap (T : Subgroup M)) m)) = ⟨x, hx⟩ := by
        have hsurj : Function.Surjective fun m => (MonoidHom.ofInjective hinj).symm
            (MulEquiv.subgroupCongr hrange ((e.subgroupMap (T : Subgroup M)) m)) :=
          (MonoidHom.ofInjective hinj).symm.surjective.comp
            ((MulEquiv.subgroupCongr hrange).surjective.comp
              (e.subgroupMap (T : Subgroup M)).surjective)
        exact hsurj ⟨x, hx⟩
      refine ⟨m, ?_⟩
      change (((MonoidHom.ofInjective hinj).symm (MulEquiv.subgroupCongr hrange
        ((e.subgroupMap (T : Subgroup M)) m)) : ↥(P : Subgroup H)) : H) = x
      rw [hm]
    · rintro _ ⟨m, rfl⟩
      exact ((MonoidHom.ofInjective hinj).symm
        (MulEquiv.subgroupCongr hrange ((e.subgroupMap (T : Subgroup M)) m))).2

end CFSG.CGT.Stroth77
