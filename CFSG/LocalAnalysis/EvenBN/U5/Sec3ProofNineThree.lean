module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBGeneric
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace S3e

open Subgroup
open scoped MatrixGroups commutatorElement
open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.LocalAnalysis.EvenBN


open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK


open Subgroup

section Prod

variable {J : Type*} [Group J] [Finite J]

theorem center_eq_bot_of_simple [IsSimpleGroup J] (hJ : ∃ x y : J, x * y ≠ y * x) :
    center J = ⊥ := by
  rcases (center J).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hJ
    have hy : y ∈ center J := by rw [h]; exact mem_top y
    exact hxy (mem_center_iff.1 hy x)

theorem hom_eq_one_or_injective [IsSimpleGroup J] {K : Type*} [Group K] (p : J →* K) :
    (∀ a, p a = 1) ∨ Function.Injective p := by
  rcases p.normal_ker.eq_bot_or_eq_top with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff p).1 h)
  · exact Or.inl fun a => MonoidHom.mem_ker.1 (h ▸ mem_top a)

theorem aut_prod_diag_odd [IsSimpleGroup J] (hJ : ∃ x y : J, x * y ≠ y * x)
    (β : MulAut (J × J)) (hdiag : ∀ a : J, β (a, a) = (a, a)) {m : ℕ} (hm : Odd m)
    (hβ : β ^ m = 1) : β = 1 := by
  have hZ := center_eq_bot_of_simple hJ
  have hcent : ∀ x : J, (∀ y : J, y * x = x * y) → x = 1 := fun x hx => by
    have : x ∈ center J := mem_center_iff.2 hx
    rw [hZ] at this
    exact mem_bot.1 this
  set p : J →* J := (MonoidHom.fst J J).comp (β.toMonoidHom.comp (MonoidHom.inl J J)) with hp
  set q : J →* J := (MonoidHom.snd J J).comp (β.toMonoidHom.comp (MonoidHom.inl J J)) with hq
  set r : J →* J := (MonoidHom.fst J J).comp (β.toMonoidHom.comp (MonoidHom.inr J J)) with hr
  set s : J →* J := (MonoidHom.snd J J).comp (β.toMonoidHom.comp (MonoidHom.inr J J)) with hs
  have hβl : ∀ a, β (a, 1) = (p a, q a) := fun a => rfl
  have hβr : ∀ a, β (1, a) = (r a, s a) := fun a => rfl
  have hsplit : ∀ a b : J, β (a, b) = (p a * r b, q a * s b) := fun a b => by
    have : ((a, b) : J × J) = (a, 1) * (1, b) := by simp
    rw [this, map_mul, hβl, hβr]
    rfl
  have hd1 : ∀ a, p a * r a = a := fun a => by
    have := hdiag a
    rw [hsplit] at this
    exact congrArg Prod.fst this
  have hd2 : ∀ a, q a * s a = a := fun a => by
    have := hdiag a
    rw [hsplit] at this
    exact congrArg Prod.snd this
  have hc : ∀ a b, (p a, q a) * (r b, s b) = (r b, s b) * (p a, q a) := fun a b => by
    rw [← hβl, ← hβr, ← map_mul, ← map_mul]
    congr 1
    simp
  have hc1 : ∀ a b, p a * r b = r b * p a := fun a b => congrArg Prod.fst (hc a b)
  have hc2 : ∀ a b, q a * s b = s b * q a := fun a b => congrArg Prod.snd (hc a b)
  have hinj1 : ∀ a, p a = 1 → q a = 1 → a = 1 := fun a h1 h2 => by
    have : β (a, 1) = β 1 := by rw [hβl, h1, h2, map_one]; rfl
    exact (Prod.mk.inj (β.injective this)).1
  have hinj2 : ∀ b, r b = 1 → s b = 1 → b = 1 := fun b h1 h2 => by
    have : β (1, b) = β 1 := by rw [hβr, h1, h2, map_one]; rfl
    exact (Prod.mk.inj (β.injective this)).2
  have hsurj : ∀ f : J →* J, Function.Injective f → Function.Surjective f := fun f hf =>
    Finite.injective_iff_surjective.1 hf
  rcases hom_eq_one_or_injective p with hp1 | hpinj
  ·
    exfalso
    have hr' : ∀ a, r a = a := fun a => by simpa [hp1 a] using hd1 a
    have hqinj : Function.Injective q := by
      refine (injective_iff_map_eq_one q).2 fun a ha => hinj1 a (hp1 a) ha
    have hs1 : ∀ b, s b = 1 := fun b => hcent _ fun y => by
      obtain ⟨a, rfl⟩ := hsurj q hqinj y
      exact hc2 a b
    have hq' : ∀ a, q a = a := fun a => by simpa [hs1 a] using hd2 a
    have hswap : ∀ a b, β (a, b) = (b, a) := fun a b => by
      rw [hsplit, hp1, hr', hq', hs1]
      simp
    have hββ : β * β = 1 := by
      ext ⟨a, b⟩ <;> simp [hswap]
    have hβ1 : β = 1 := by
      obtain ⟨k, rfl⟩ := hm
      calc β = β ^ (2 * k + 1) := by
            rw [pow_succ, pow_mul, sq, hββ, one_pow, one_mul]
        _ = 1 := hβ
    obtain ⟨x, y, hxy⟩ := hJ
    have hx1 : x ≠ 1 := fun h => hxy (by rw [h, one_mul, mul_one])
    have h2 := hswap x 1
    rw [hβ1] at h2
    exact hx1 (congrArg Prod.fst (h2.trans rfl)).symm.symm |> fun h => by
      have := congrArg Prod.snd h2
      exact hx1 (by simpa using this.symm)
  ·
    have hpsurj := hsurj p hpinj
    have hr1 : ∀ b, r b = 1 := fun b => hcent _ fun y => by
      obtain ⟨a, rfl⟩ := hpsurj y
      exact (hc1 a b)
    have hp' : ∀ a, p a = a := fun a => by simpa [hr1 a] using hd1 a
    have hsinj : Function.Injective s := by
      refine (injective_iff_map_eq_one s).2 fun b hb => hinj2 b (hr1 b) hb
    have hq1 : ∀ a, q a = 1 := fun a => hcent _ fun y => by
      obtain ⟨b, rfl⟩ := hsurj s hsinj y
      exact (hc2 a b).symm
    have hs' : ∀ a, s a = a := fun a => by simpa [hq1 a] using hd2 a
    ext ⟨a, b⟩
    · simp [hsplit, hp', hr1, hq1, hs']
    · simp [hsplit, hp', hr1, hq1, hs']


open scoped commutatorElement in
theorem commutator_eq_top_of_simple [IsSimpleGroup J] (hJ : ∃ x y : J, x * y ≠ y * x) :
    ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
  have hn : (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ : Subgroup J).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hJ
    have : ⁅x, y⁆ ∈ (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ : Subgroup J) :=
      Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hxy this
  · exact h

open scoped commutatorElement in
theorem prod_normal_diag_top [IsSimpleGroup J] (hJ : ∃ x y : J, x * y ≠ y * x)
    (N : Subgroup (J × J)) [N.Normal] (hdiag : ∀ a : J, (a, a) ∈ N) : N = ⊤ := by
  have hc1 : ∀ a b : J, (⁅a, b⁆, (1 : J)) ∈ N := by
    intro a b
    have h1 : ((a, 1) : J × J) * (b, b) * (a, 1)⁻¹ ∈ N := Normal.conj_mem inferInstance _ (hdiag b) _
    have h2 := mul_mem h1 (inv_mem (hdiag b))
    convert h2 using 1
    ext <;> simp [commutatorElement_def]
  have hc2 : ∀ a b : J, ((1 : J), ⁅a, b⁆) ∈ N := by
    intro a b
    have h1 : ((1, a) : J × J) * (b, b) * (1, a)⁻¹ ∈ N := Normal.conj_mem inferInstance _ (hdiag b) _
    have h2 := mul_mem h1 (inv_mem (hdiag b))
    convert h2 using 1
    ext <;> simp [commutatorElement_def]
  have hperf := commutator_eq_top_of_simple hJ
  have hl : ∀ c : J, (c, (1 : J)) ∈ N := by
    intro c
    have : (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ : Subgroup J) ≤ N.comap (MonoidHom.inl J J) := by
      rw [Subgroup.commutator_le]
      intro g _ g' _
      exact hc1 g g'
    have hc : c ∈ N.comap (MonoidHom.inl J J) := this (by rw [hperf]; exact mem_top c)
    exact hc
  have hr : ∀ c : J, ((1 : J), c) ∈ N := by
    intro c
    have : (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ : Subgroup J) ≤ N.comap (MonoidHom.inr J J) := by
      rw [Subgroup.commutator_le]
      intro g _ g' _
      exact hc2 g g'
    have hc : c ∈ N.comap (MonoidHom.inr J J) := this (by rw [hperf]; exact mem_top c)
    exact hc
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have := mul_mem (hl a) (hr b)
  simpa using this

end Prod


section LayerProd

variable {X : Type} [Group X] [Finite X] {J Λ : Subgroup X} [Λ.Normal] {t : X} {e : ℕ}

theorem layerSide_prod [IsSimpleGroup J] (hJnab : ∃ x y : J, x * y ≠ y * x)
    (hinv : ∃ x : J, x * x = 1 ∧ x ≠ 1) (hJΛ : J ≤ Λ)
    (hfaith : ∀ z : X, (∀ d ∈ Λ, z * d * z⁻¹ = d) → z = 1) (ψ : Λ ≃* J × J)
    (hdiag : ∀ (j : X) (hjJ : j ∈ J) (hjΛ : j ∈ Λ), ψ ⟨j, hjΛ⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩))
    (hswap : ∀ (d : X) (hd : d ∈ Λ) (hdt : t⁻¹ * d * t ∈ Λ),
      ψ ⟨t⁻¹ * d * t, hdt⟩ = (ψ ⟨d, hd⟩).swap) :
    (∃ u ∈ Λ, orderOf u = 2 ∧ u * (t⁻¹ * u * t) = (t⁻¹ * u * t) * u ∧
      u * (t⁻¹ * u * t) ≠ 1 ∧ u * (t⁻¹ * u * t) ∈ J) ∧
    (∀ z : X, (∀ j ∈ J, z * j = j * z) → Odd (orderOf z) → z = 1) ∧
    (∀ N : Subgroup X, J ≤ N → N ≤ Λ → (∀ g ∈ Λ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → N = Λ) ∧
    Nat.card Λ = Nat.card J ^ 2 := by
  have hdiag' : ∀ j : J, ψ ⟨j, hJΛ j.2⟩ = (j, j) := fun j => hdiag j j.2 (hJΛ j.2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx2, hx1⟩ := hinv
    set u : Λ := ψ.symm (x, 1) with hu
    have hu' : ψ u = (x, 1) := by rw [hu, MulEquiv.apply_symm_apply]
    have htu : t⁻¹ * (u : X) * t ∈ Λ := by
      have := Normal.conj_mem (inferInstance : Λ.Normal) (u : X) u.2 t⁻¹
      simpa using this
    set v : Λ := ⟨t⁻¹ * (u : X) * t, htu⟩ with hv
    have hv' : ψ v = (1, x) := by
      have := hswap (u : X) u.2 htu
      rw [hv]
      have e : (⟨(u : X), u.2⟩ : Λ) = u := rfl
      rw [e, hu'] at this
      simpa using this
    have huv : u * v = ⟨(x : X), hJΛ x.2⟩ := by
      apply ψ.injective
      rw [map_mul, hu', hv', hdiag']
      simp
    have hvu : v * u = ⟨(x : X), hJΛ x.2⟩ := by
      apply ψ.injective
      rw [map_mul, hu', hv', hdiag']
      simp
    refine ⟨u, u.2, ?_, ?_, ?_, ?_⟩
    · have hu2 : u * u = 1 := by
        apply ψ.injective
        rw [map_mul, hu', map_one]
        simp [hx2]
      have hne : (u : X) ≠ 1 := fun h => hx1 (by
        have : u = 1 := Subtype.ext h
        rw [this, map_one] at hu'
        have := congrArg Prod.fst hu'
        exact this.symm)
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val hu2) hne
    · have : u * v = v * u := by rw [huv, hvu]
      exact congrArg Subtype.val this
    · intro h
      have : u * v = 1 := Subtype.ext h
      rw [huv] at this
      apply hx1
      have := congrArg Subtype.val this
      exact Subtype.ext this
    · have : (u : X) * (t⁻¹ * (u : X) * t) = ((u * v : Λ) : X) := rfl
      rw [this, huv]
      exact x.2
  · intro z hz hm
    set m := orderOf z with hmdef
    have hzm : z ^ m = 1 := pow_orderOf_eq_one z
    set β : MulAut Λ := MulAut.conjNormal z with hβ
    set β' : MulAut (J × J) := MulAut.congr ψ β with hβ'
    have hβ'x : ∀ y, β' y = ψ (β (ψ.symm y)) := fun y => rfl
    have hfix : ∀ a : J, β' (a, a) = (a, a) := by
      intro a
      have : ψ.symm (a, a) = ⟨(a : X), hJΛ a.2⟩ := by
        rw [MulEquiv.symm_apply_eq, hdiag']
      rw [hβ'x, this]
      have : β ⟨(a : X), hJΛ a.2⟩ = ⟨(a : X), hJΛ a.2⟩ := by
        apply Subtype.ext
        rw [hβ, MulAut.conjNormal_apply]
        calc z * (a : X) * z⁻¹ = (a : X) * z * z⁻¹ := by rw [hz _ a.2]
          _ = a := by group
      rw [this, hdiag']
    have hβm : β' ^ m = 1 := by
      rw [hβ', ← map_pow, hβ, ← map_pow, hzm, map_one, map_one]
    have h1 := aut_prod_diag_odd hJnab β' hfix hm hβm
    refine hfaith z fun d hd => ?_
    have h2 : β' = 1 := h1
    have h3 := congrArg (fun b : MulAut (J × J) => b (ψ ⟨d, hd⟩)) h2
    simp only [hβ'x, MulEquiv.symm_apply_apply, MulAut.one_apply] at h3
    have h4 := ψ.injective h3
    have h5 := congrArg (fun a : Λ => (a : X)) h4
    simpa [hβ, MulAut.conjNormal_apply] using h5
  · intro N hJN hNΛ hNinv
    set N' : Subgroup (J × J) := (N.subgroupOf Λ).map ψ.toMonoidHom with hN'
    haveI : N'.Normal := ⟨by
      rintro _ ⟨n, hn, rfl⟩ g
      obtain ⟨g₀, rfl⟩ := ψ.surjective g
      refine ⟨g₀ * n * g₀⁻¹, ?_, by simp⟩
      exact hNinv g₀ g₀.2 n hn⟩
    have hdiagN : ∀ a : J, (a, a) ∈ N' := fun a =>
      ⟨⟨(a : X), hJΛ a.2⟩, hJN a.2, hdiag' a⟩
    have htop := prod_normal_diag_top hJnab N' hdiagN
    refine le_antisymm hNΛ fun x hx => ?_
    have : ψ ⟨x, hx⟩ ∈ N' := by rw [htop]; exact mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have : y = ⟨x, hx⟩ := ψ.injective hyx
    rw [this] at hy
    exact hy
  · rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, sq]

end LayerProd




open Subgroup
open scoped MatrixGroups
open CFSG.LocalAnalysis.EvenBN
open CFSG.LocalAnalysis.EvenBN.GMSK (sl2_exists_mul_ne)

section Sl2

variable {F : Type*} [Field F]

theorem eq_one_of_mul_self_eq_one_char_two (h2 : (2 : F) = 0) {a : F} (h : a * a = 1) :
    a = 1 := by
  have : (a - 1) * (a - 1) = 0 := by linear_combination h + (1 - a) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 this)

theorem aux_comm_entries (h2 : (2 : F) = 0) (a b c d p q r s p' q' r' s' : F)
    (e00 : a * a + b * c = 1) (e01 : a * b + b * d = 0) (e10 : c * a + d * c = 0)
    (e11 : c * b + d * d = 1) (hg1' : ¬(a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1))
    (x00 : p * a + q * c = a * p + b * r) (x01 : p * b + q * d = a * q + b * s)
    (x10 : r * a + s * c = c * p + d * r) (x11 : r * b + s * d = c * q + d * s)
    (y00 : p' * a + q' * c = a * p' + b * r') (y01 : p' * b + q' * d = a * q' + b * s')
    (y10 : r' * a + s' * c = c * p' + d * r') (y11 : r' * b + s' * d = c * q' + d * s') :
    p * p' + q * r' = p' * p + q' * r ∧ p * q' + q * s' = p' * q + q' * s ∧
      r * p' + s * r' = r' * p + s' * r ∧ r * q' + s * s' = r' * q + s' * s := by
  have hda : d = a := by
    by_contra hne
    have hs : a + d ≠ 0 := fun h => hne (by linear_combination h - a * h2 + (0 : F) * h)
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    subst hb hc
    have ha : a = 1 := eq_one_of_mul_self_eq_one_char_two h2 (by linear_combination e00)
    have hd : d = 1 := eq_one_of_mul_self_eq_one_char_two h2 (by linear_combination e11)
    exact hg1' ⟨ha, rfl, rfl, hd⟩
  subst hda
  by_cases hb : b = 0
  · subst hb
    have hc : c ≠ 0 := by
      intro hc
      subst hc
      exact hg1' ⟨eq_one_of_mul_self_eq_one_char_two h2 (by linear_combination e00), rfl, rfl,
        eq_one_of_mul_self_eq_one_char_two h2 (by linear_combination e11)⟩
    have hq : q = 0 := by
      have : c * q = 0 := by linear_combination -x11
      exact (mul_eq_zero.1 this).resolve_left hc
    have hq' : q' = 0 := by
      have : c * q' = 0 := by linear_combination -y11
      exact (mul_eq_zero.1 this).resolve_left hc
    have hsp : s = p := by
      have : c * (s - p) = 0 := by linear_combination x10
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc)
    have hsp' : s' = p' := by
      have : c * (s' - p') = 0 := by linear_combination y10
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc)
    subst hq hq' hsp hsp'
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  · have hsp : s = p := by
      have : b * (s - p) = 0 := by linear_combination -x01
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hb)
    have hsp' : s' = p' := by
      have : b * (s' - p') = 0 := by linear_combination -y01
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hb)
    have hqr : q * r' = q' * r := by
      have : b * (q * r' - q' * r) = 0 := by linear_combination q * y11 - q' * x11
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hb)
    have hrq : r * q' = r' * q := by
      have : b * (r * q' - r' * q) = 0 := by linear_combination q' * x11 - q * y11
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hb)
    subst hsp hsp'
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination hqr
    · ring
    · ring
    · linear_combination hrq

theorem sl2_centralizer_involution_comm (h2 : (2 : F) = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (hgg : g * g = 1) (hg1 : g ≠ 1)
    (x y : Matrix.SpecialLinearGroup (Fin 2) F) (hx : x * g = g * x) (hy : y * g = g * y) :
    x * y = y * x := by
  have hgm : (g : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hgg
    simpa using this
  have hxm : (x : Matrix (Fin 2) (Fin 2) F) * g = g * x := by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hx
    simpa using this
  have hym : (y : Matrix (Fin 2) (Fin 2) F) * g = g * y := by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hy
    simpa using this
  have hgdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hgdet
  have hg1' : ¬ ((g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1) := by
    rintro ⟨h00, h01, h10, h11⟩
    apply hg1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have e00 := congrFun (congrFun hgm 0) 0
  have e01 := congrFun (congrFun hgm 0) 1
  have e10 := congrFun (congrFun hgm 1) 0
  have e11 := congrFun (congrFun hgm 1) 1
  have x00 := congrFun (congrFun hxm 0) 0
  have x01 := congrFun (congrFun hxm 0) 1
  have x10 := congrFun (congrFun hxm 1) 0
  have x11 := congrFun (congrFun hxm 1) 1
  have y00 := congrFun (congrFun hym 0) 0
  have y01 := congrFun (congrFun hym 0) 1
  have y10 := congrFun (congrFun hym 1) 0
  have y11 := congrFun (congrFun hym 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.isValue, Fin.zero_eta, Fin.mk_one, one_ne_zero, not_false_eq_true, zero_ne_one] at e00 e01 e10 e11 x00 x01 x10 x11 y00 y01 y10 y11
  obtain ⟨k00, k01, k10, k11⟩ := aux_comm_entries h2 _ _ _ _ _ _ _ _ _ _ _ _ e00 e01 e10 e11 hg1'
    x00 x01 x10 x11 y00 y01 y10 y11
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k00
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k01
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k10
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using k11

end Sl2



section Fix

variable {F : Type*} [Field F]

@[expose] def frobPow (F : Type*) [Field F] [CharP F 2] (e : ℕ) : F →+* F :=
  haveI : ExpChar F 2 := ExpChar.prime Nat.prime_two
  iterateFrobenius F 2 e

theorem frobPow_apply [CharP F 2] (e : ℕ) (c : F) : frobPow F e c = c ^ 2 ^ e := by
  rfl

@[expose] def fixSL (F : Type*) [Field F] [CharP F 2] (e : ℕ) : Subgroup SL(2, F) :=
  MonoidHom.eqLocus (Matrix.SpecialLinearGroup.map (frobPow F e)) (MonoidHom.id _)

theorem mem_fixSL_iff [CharP F 2] {e : ℕ} {g : SL(2, F)} :
    g ∈ fixSL F e ↔ ∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ e =
      (g : Matrix (Fin 2) (Fin 2) F) i j := by
  change Matrix.SpecialLinearGroup.map (frobPow F e) g = g ↔ _
  rw [Matrix.SpecialLinearGroup.ext_iff]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    frobPow_apply]

end Fix

section Simple

variable {X : Type} [Group X] [Finite X] {Λ J : Subgroup X} [Λ.Normal] {t : X}
  {F : Type} [Field F] [Finite F]

theorem not_inner_of_centralizer_nonabelian [CharP F 2] (ι : Λ ≃* SL(2, F))
    (hfaith : ∀ z : X, (∀ d ∈ Λ, z * d * z⁻¹ = d) → z = 1) (ht2 : orderOf t = 2)
    (hJΛ : J ≤ Λ) (htJ : ∀ j ∈ J, t * j = j * t) (hJnab : ∃ x y : J, x * y ≠ y * x) :
    (MulAut.conjNormal t : MulAut Λ) ∉ (MulAut.conj : Λ →* MulAut Λ).range := by
  rintro ⟨k, hk⟩
  have hkx : ∀ x : Λ, (k : X) * x * (k : X)⁻¹ = t * x * t⁻¹ := fun x => by
    have := congrArg (fun a : MulAut Λ => ((a x : Λ) : X)) hk
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this
  have htk : t = k := by
    have h1 : (k : X)⁻¹ * t = 1 := by
      refine hfaith _ fun d hd => ?_
      have := hkx ⟨d, hd⟩
      simp only at this
      calc (k : X)⁻¹ * t * d * ((k : X)⁻¹ * t)⁻¹ = (k : X)⁻¹ * (t * d * t⁻¹) * k := by group
        _ = d := by rw [← this]; group
    exact (inv_mul_eq_one.1 h1).symm
  subst htk
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set g : SL(2, F) := ι k with hg
  have hgg : g * g = 1 := by
    rw [hg, ← map_mul]
    have : k * k = 1 := by
      have : (k : X) * k = 1 := by
        rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one _
      exact Subtype.ext this
    rw [this, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    have : k = 1 := ι.injective (h.trans (map_one ι).symm)
    have h1 : (k : X) = 1 := by rw [this]; rfl
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨x, y, hxy⟩ := hJnab
  apply hxy
  have hcomm : ∀ j : J, ι ⟨j, hJΛ j.2⟩ * g = g * ι ⟨j, hJΛ j.2⟩ := fun j => by
    rw [hg, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (htJ j j.2).symm
  have h3 := sl2_centralizer_involution_comm h2 g hgg hg1 _ _ (hcomm x) (hcomm y)
  have h4 : (⟨x, hJΛ x.2⟩ : Λ) * ⟨y, hJΛ y.2⟩ = ⟨y, hJΛ y.2⟩ * ⟨x, hJΛ x.2⟩ :=
    ι.injective (by rw [map_mul, map_mul]; exact h3)
  have h5 := congrArg (fun a : Λ => (a : X)) h4
  exact Subtype.ext (by simpa using h5)


theorem simple_normal_form [CharP F 2] {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ (2 * e))
    (ι : Λ ≃* SL(2, F)) (hfaith : ∀ z : X, (∀ d ∈ Λ, z * d * z⁻¹ = d) → z = 1)
    (ht2 : orderOf t = 2) (hJΛ : J ≤ Λ) (htJ : ∀ j ∈ J, t * j = j * t)
    (hJnab : ∃ x y : J, x * y ≠ y * x) :
    ∃ ψ : Λ ≃* SL(2, F), ∀ x : Λ,
      ((ψ (MulAut.conjNormal t x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (ψ x : Matrix (Fin 2) (Fin 2) F).map (fun c => c ^ 2 ^ e) := by
  have hαα : (MulAut.conjNormal t : MulAut Λ) * MulAut.conjNormal t = 1 := by
    rw [← map_mul, ← pow_two, ← ht2, pow_orderOf_eq_one, map_one]
  obtain ⟨e', hee', ψ, hψ⟩ := GMS.exists_frobenius_normal_form (f := 2 * e) (by omega) hF ι
    (MulAut.conjNormal t) hαα
    (not_inner_of_centralizer_nonabelian ι hfaith ht2 hJΛ htJ hJnab)
  have : e' = e := by omega
  subst this
  exact ⟨ψ, hψ⟩


theorem simple_fixed_eq [CharP F 2] {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ (2 * e))
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ e) (φJ : J ≃* SL(2, k))
    (hJΛ : J ≤ Λ) (htJ : ∀ j ∈ J, t * j = j * t) (ψ : Λ ≃* SL(2, F))
    (hψ : ∀ x : Λ, ((ψ (MulAut.conjNormal t x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (ψ x : Matrix (Fin 2) (Fin 2) F).map (fun c => c ^ 2 ^ e)) :
    (J.subgroupOf Λ).map ψ.toMonoidHom = fixSL F e := by
  have hle : (J.subgroupOf Λ).map ψ.toMonoidHom ≤ fixSL F e := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSL_iff]
    intro i j
    have hxJ : (x : X) ∈ J := hx
    have hfix : (MulAut.conjNormal t x : Λ) = x := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      calc t * (x : X) * t⁻¹ = (x : X) * t * t⁻¹ := by rw [htJ _ hxJ]
        _ = x := by group
    have := hψ x
    rw [hfix] at this
    have h2 := congrFun (congrFun this i) j
    simpa [Matrix.map_apply] using h2.symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := GMS.card_le_of_frobenius_fixed he hF hk (fixSL F e) fun g hg => mem_fixSL_iff.1 hg
  have h2 : Nat.card ((J.subgroupOf Λ).map ψ.toMonoidHom) = Nat.card SL(2, k) := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    rw [← Nat.card_congr φJ.toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJΛ).toEquiv
  rw [h2]
  exact h1


open CFSG.CGT.Timmesfeld75 in
theorem exists_not_frob_fixed [CharP F 2] {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ (2 * e)) :
    ∃ s : F, s ^ 2 ^ e ≠ s := by
  by_contra hall
  push Not at hall
  have h1 := GMS.natCard_subfield_le_of_pow_two_pow_eq he (⊤ : Subfield F) fun c _ => hall c
  have h2 : Nat.card (⊤ : Subfield F) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [h2, hF] at h1
  have : 2 ^ e < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

open CFSG.CGT.Timmesfeld75 in
theorem simple_exists_u [CharP F 2] {e : ℕ} (he : 1 ≤ e) (hF : Nat.card F = 2 ^ (2 * e))
    (ψ : Λ ≃* SL(2, F)) (ht2 : t * t = 1)
    (hψ : ∀ x : Λ, ((ψ (MulAut.conjNormal t x) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (ψ x : Matrix (Fin 2) (Fin 2) F).map (fun c => c ^ 2 ^ e))
    (hY : (J.subgroupOf Λ).map ψ.toMonoidHom = fixSL F e) :
    ∃ u ∈ Λ, orderOf u = 2 ∧ u * (t⁻¹ * u * t) = (t⁻¹ * u * t) * u ∧
      u * (t⁻¹ * u * t) ≠ 1 ∧ u * (t⁻¹ * u * t) ∈ J := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨s, hs⟩ := exists_not_frob_fixed he hF
  set s' : F := s ^ 2 ^ e with hs'
  have hss : s' ^ 2 ^ e = s := by
    haveI := Fintype.ofFinite F
    have : Fintype.card F = 2 ^ (2 * e) := by rw [← Nat.card_eq_fintype_card, hF]
    rw [hs', ← pow_mul, ← pow_add, ← two_mul, ← this]
    exact FiniteField.pow_card s
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simp [hs', h]
  set u₀ : Λ := ψ.symm (utriElt s) with hu₀
  have hαu : ψ (MulAut.conjNormal t u₀) = utriElt s' := by
    apply Subtype.ext
    rw [hψ, hu₀, MulEquiv.apply_symm_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11, hs']
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : (t⁻¹ * (u₀ : X) * t : X) = (MulAut.conjNormal t u₀ : Λ) := by
    rw [MulAut.conjNormal_apply, htinv]
  refine ⟨u₀, u₀.2, ?_, ?_, ?_, ?_⟩
  ·
    have hu1 : u₀ * u₀ = 1 := by
      apply ψ.injective
      rw [map_mul, hu₀, MulEquiv.apply_symm_apply, utriElt_mul_self, map_one]
    have hu1' : (u₀ : X) * u₀ = 1 := congrArg Subtype.val hu1
    have hne : (u₀ : X) ≠ 1 := fun h => hs0 (by
      have hu1'' : u₀ = 1 := Subtype.ext h
      have h3 := congrArg ψ hu1''
      rw [hu₀, MulEquiv.apply_symm_apply, map_one] at h3
      exact utriElt_injective (h3.trans utriElt_zero.symm))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [← pow_two] at hu1') hne
  ·
    rw [hconj]
    have : u₀ * MulAut.conjNormal t u₀ = MulAut.conjNormal t u₀ * u₀ := by
      apply ψ.injective
      rw [map_mul, map_mul, hαu, hu₀, MulEquiv.apply_symm_apply, ← utriElt_add, ← utriElt_add,
        add_comm]
    exact congrArg Subtype.val this
  ·
    rw [hconj]
    intro h
    have h1 : u₀ * MulAut.conjNormal t u₀ = 1 := Subtype.ext h
    have h3 := congrArg ψ h1
    rw [map_mul, hαu, hu₀, MulEquiv.apply_symm_apply, ← utriElt_add, map_one] at h3
    have h4 := utriElt_injective (h3.trans utriElt_zero.symm)
    apply hs
    linear_combination h4 - s * h2
  ·
    rw [hconj]
    have hmem : ψ (u₀ * MulAut.conjNormal t u₀) ∈ fixSL F e := by
      rw [map_mul, hαu, hu₀, MulEquiv.apply_symm_apply, ← utriElt_add, mem_fixSL_iff]
      intro i j
      have hadd : (s + s') ^ 2 ^ e = s + s' := by
        rw [add_pow_char_pow, hss, add_comm]
      fin_cases i <;> fin_cases j <;> simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
        utriElt_apply_11, hadd]
    rw [← hY] at hmem
    obtain ⟨y, hy, hyψ⟩ := hmem
    have : y = u₀ * MulAut.conjNormal t u₀ := ψ.injective hyψ
    have hyJ : (y : X) ∈ J := hy
    rw [this] at hyJ
    exact hyJ


open CFSG.CGT.Timmesfeld75 in
theorem eq_one_of_commute_unitri [CharP F 2] (g : SL(2, F)) (hU : g * utriElt 1 = utriElt 1 * g)
    (hL : g * ltriElt 1 = ltriElt 1 * g) : g = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hUm := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hU
  have hLm := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hL
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hUm hLm
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have u00 := congrFun (congrFun hUm 0) 0
  have u01 := congrFun (congrFun hUm 0) 1
  have u10 := congrFun (congrFun hUm 1) 0
  have u11 := congrFun (congrFun hUm 1) 1
  have l00 := congrFun (congrFun hLm 0) 0
  have l01 := congrFun (congrFun hLm 0) 1
  have l10 := congrFun (congrFun hLm 1) 0
  have l11 := congrFun (congrFun hLm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
    utriElt_apply_11, ltriElt] at u00 u01 u10 u11 l00 l01 l10 l11
  have hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination u00
  have hb : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination l00
  have hda : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -u01
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    refine eq_one_of_mul_self_eq_one_char_two h2 ?_
    rw [hb, hc] at hdet
    rw [hda] at hdet
    linear_combination hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hda]


theorem fieldAut_sq_of_fixes [CharP F 2] {e : ℕ} (hF : Nat.card F = 2 ^ (2 * e)) (σ : F ≃+* F)
    (hσ : ∀ c : F, c ^ 2 ^ e = c → σ c = c) (c : F) : σ (σ c) = c := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  haveI := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ (2 * e) := by rw [← Nat.card_eq_fintype_card, hF]
  have hss : ∀ a : F, (a ^ 2 ^ e) ^ 2 ^ e = a := fun a => by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hcard]
    exact FiniteField.pow_card a
  set c' : F := c ^ 2 ^ e with hc'
  have ht : (c + c') ^ 2 ^ e = c + c' := by
    rw [add_pow_char_pow, hss, add_comm]
  have hn : (c * c') ^ 2 ^ e = c * c' := by
    rw [mul_pow, hss, mul_comm]
  have hσt := hσ _ ht
  have hσn := hσ _ hn
  rw [map_add] at hσt
  rw [map_mul] at hσn
  have hroot : c * c + (c + c') * c + c * c' = 0 := by
    linear_combination (c * c + c * c') * h2
  have hσroot := congrArg σ hroot
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_add, hσt, hσn, map_zero] at hσroot
  have hprod : (σ c + c) * (σ c + c') = 0 := by
    linear_combination hσroot
  rcases mul_eq_zero.1 hprod with h | h
  · have hσc : σ c = c := by linear_combination h - c * h2
    rw [hσc, hσc]
  · have hσc : σ c = c' := by linear_combination h - c' * h2
    rw [hσc]
    have : σ c' = (σ c) ^ 2 ^ e := by rw [hc', map_pow]
    rw [this, hσc, hss]


open CFSG.CGT.Timmesfeld75 in
theorem simple_odd_centralizer [CharP F 2] {e : ℕ} (hF : Nat.card F = 2 ^ (2 * e))
    (ψ : Λ ≃* SL(2, F)) (hY : (J.subgroupOf Λ).map ψ.toMonoidHom = fixSL F e)
    (hfaith : ∀ z : X, (∀ d ∈ Λ, z * d * z⁻¹ = d) → z = 1)
    {z : X} (hz : ∀ j ∈ J, z * j = j * z) {m : ℕ} (hm : Odd m) (hzm : z ^ m = 1) : z = 1 := by
  set β : MulAut Λ := MulAut.conjNormal z with hβ
  set β' : SL(2, F) ≃* SL(2, F) := (ψ.symm.trans β).trans ψ with hβ'
  have hβ'apply : ∀ y, β' y = ψ (β (ψ.symm y)) := fun y => rfl
  have hfix : ∀ y ∈ fixSL F e, β' y = y := by
    intro y hy
    rw [← hY] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxJ : (x : X) ∈ J := hx
    have : β x = x := by
      apply Subtype.ext
      rw [hβ, MulAut.conjNormal_apply]
      calc z * (x : X) * z⁻¹ = (x : X) * z * z⁻¹ := by rw [hz _ hxJ]
        _ = x := by group
    rw [hβ'apply]
    change ψ (β (ψ.symm (ψ x))) = ψ x
    rw [MulEquiv.symm_apply_apply, this]
  obtain ⟨g, σ, hg⟩ := exists_eq_conj_sl2FieldAut β'
  have hu1 : (utriElt 1 : SL(2, F)) ∈ fixSL F e := by
    rw [mem_fixSL_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11]
  have hl1 : (ltriElt 1 : SL(2, F)) ∈ fixSL F e := by
    rw [mem_fixSL_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ltriElt]
  have hg1 : g = 1 := by
    apply eq_one_of_commute_unitri
    · have h1 := hfix _ hu1
      rw [hg, sl2FieldAut_utriElt, map_one] at h1
      calc g * utriElt 1 = g * utriElt 1 * g⁻¹ * g := by group
        _ = utriElt 1 * g := by rw [h1]
    · have h1 := hfix _ hl1
      rw [hg, sl2FieldAut_ltriElt, map_one] at h1
      calc g * ltriElt 1 = g * ltriElt 1 * g⁻¹ * g := by group
        _ = ltriElt 1 * g := by rw [h1]
  subst hg1
  have hσ : ∀ c : F, c ^ 2 ^ e = c → σ c = c := by
    intro c hc
    have hmem : (utriElt c : SL(2, F)) ∈ fixSL F e := by
      rw [mem_fixSL_iff]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
        utriElt_apply_11, hc]
    have h1 := hfix _ hmem
    rw [hg, one_mul, inv_one, mul_one, sl2FieldAut_utriElt] at h1
    exact utriElt_injective h1
  have hσσ := fieldAut_sq_of_fixes hF σ hσ
  have hββ' : ∀ y, β' (β' y) = y := by
    intro y
    rw [hg, hg]
    simp only [one_mul, inv_one, mul_one]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [sl2FieldAut_eq_map, Matrix.SpecialLinearGroup.map_apply_coe, hσσ]
  have hββ : β * β = 1 := by
    refine MulEquiv.ext fun x => ?_
    apply ψ.injective
    have := hββ' (ψ x)
    rw [hβ'apply, hβ'apply] at this
    simpa using this
  have hβm : β ^ m = 1 := by
    rw [hβ, ← map_pow, hzm, map_one]
  have hβ1 : β = 1 := by
    obtain ⟨k, rfl⟩ := hm
    calc β = β ^ (2 * k + 1) := by
          rw [pow_succ, pow_mul, sq, hββ, one_pow, one_mul]
      _ = 1 := hβm
  refine hfaith z fun d hd => ?_
  have := congrArg (fun a : MulAut Λ => ((a ⟨d, hd⟩ : Λ) : X)) hβ1
  simpa [hβ, MulAut.conjNormal_apply] using this


theorem layerSide_simple [CharP F 2] {e : ℕ} (he : 2 ≤ e) (hF : Nat.card F = 2 ^ (2 * e))
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ e) (φJ : J ≃* SL(2, k))
    (ι : Λ ≃* SL(2, F)) (hfaith : ∀ z : X, (∀ d ∈ Λ, z * d * z⁻¹ = d) → z = 1)
    (ht2 : orderOf t = 2) (hJΛ : J ≤ Λ) (htJ : ∀ j ∈ J, t * j = j * t) :
    (∃ u ∈ Λ, orderOf u = 2 ∧ u * (t⁻¹ * u * t) = (t⁻¹ * u * t) * u ∧
      u * (t⁻¹ * u * t) ≠ 1 ∧ u * (t⁻¹ * u * t) ∈ J) ∧
    (∀ z : X, (∀ j ∈ J, z * j = j * z) → Odd (orderOf z) → z = 1) ∧
    (∀ N : Subgroup X, J ≤ N → N ≤ Λ → (∀ g ∈ Λ, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → N = Λ) ∧
    Nat.card Λ = 2 ^ (2 * e) * ((2 ^ (2 * e)) ^ 2 - 1) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hJnab : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := k)
    refine ⟨φJ.symm x, φJ.symm y, fun h => hxy ?_⟩
    simpa using congrArg φJ h
  obtain ⟨ψ, hψ⟩ := simple_normal_form (by omega) hF ι hfaith ht2 hJΛ htJ hJnab
  have hY := simple_fixed_eq (by omega) hF hk φJ hJΛ htJ ψ hψ
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  refine ⟨simple_exists_u (by omega) hF ψ htt hψ hY, ?_, ?_, ?_⟩
  · intro z hz hm
    exact simple_odd_centralizer hF ψ hY hfaith hz hm (pow_orderOf_eq_one z)
  · intro N hJN hNΛ hNinv
    haveI : Fintype F := Fintype.ofFinite F
    have hcardF : Fintype.card F = 2 ^ (2 * e) := by rw [← Nat.card_eq_fintype_card, hF]
    have hsimple : IsSimpleGroup Λ := by
      have : IsSimpleGroup (SL(2, F)) := GMSK.sl2_isSimpleGroup h2 (by
        rw [hcardF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega))
      exact ι.isSimpleGroup
    have hnorm : (N.subgroupOf Λ).Normal := ⟨by
      intro n hn g
      rw [mem_subgroupOf] at hn ⊢
      simpa using hNinv g g.2 n hn⟩
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hJnab
      have hx1 : x ≠ 1 ∨ y ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hxy (by rw [hcon.1, hcon.2])
      have hJ1 : ∃ j : J, j ≠ 1 := by
        rcases hx1 with h1 | h1
        · exact ⟨x, h1⟩
        · exact ⟨y, h1⟩
      obtain ⟨j, hj⟩ := hJ1
      have hjN : (⟨(j : X), hJΛ j.2⟩ : Λ) ∈ N.subgroupOf Λ := hJN j.2
      rw [h, mem_bot] at hjN
      exact hj (Subtype.ext (by simpa using congrArg (fun a : Λ => (a : X)) hjN))
    · refine le_antisymm hNΛ fun x hx => ?_
      have : (⟨x, hx⟩ : Λ) ∈ N.subgroupOf Λ := by rw [h]; exact mem_top _
      exact this
  · rw [Nat.card_congr ι.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]

end Simple



section Combine

@[expose] def cardProd (e : ℕ) : ℕ := (2 ^ e * ((2 ^ e) ^ 2 - 1)) ^ 2

@[expose] def cardSimple (e : ℕ) : ℕ := 2 ^ (2 * e) * ((2 ^ (2 * e)) ^ 2 - 1)

structure LayerSide (X : Type) [Group X] (J : Subgroup X) (t : X) (e : ℕ) : Prop where
  J_le : J ≤ CFSG.layer X
  closure_eq : normalClosure (J : Set X) = CFSG.layer X
  faithful : ∀ z : X, (∀ d ∈ CFSG.layer X, z * d * z⁻¹ = d) → z = 1
  exists_u : ∃ u ∈ CFSG.layer X, orderOf u = 2 ∧ u * (t⁻¹ * u * t) = (t⁻¹ * u * t) * u ∧
    u * (t⁻¹ * u * t) ≠ 1 ∧ u * (t⁻¹ * u * t) ∈ J
  odd_centralizer : ∀ z : X, (∀ j ∈ J, z * j = j * z) → Odd (orderOf z) → z = 1
  closure_in : ∀ N : Subgroup X, J ≤ N → N ≤ CFSG.layer X →
    (∀ g ∈ CFSG.layer X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → N = CFSG.layer X
  card : Nat.card (CFSG.layer X) = cardProd e ∨ Nat.card (CFSG.layer X) = cardSimple e

theorem not_isSimpleGroup_prod' {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Nontrivial G₁]
    [Nontrivial G₂] : ¬ IsSimpleGroup (G₁ × G₂) := by
  intro hs
  obtain ⟨g₁, hg₁⟩ := exists_ne (1 : G₁)
  obtain ⟨g₂, hg₂⟩ := exists_ne (1 : G₂)
  rcases (MonoidHom.normal_ker (MonoidHom.snd G₁ G₂)).eq_bot_or_eq_top with h1 | h1
  · have : ((g₁, 1) : G₁ × G₂) ∈ (MonoidHom.snd G₁ G₂).ker := MonoidHom.mem_ker.2 rfl
    rw [h1, mem_bot] at this
    exact hg₁ (congrArg Prod.fst this)
  · have : ((1, g₂) : G₁ × G₂) ∈ (MonoidHom.snd G₁ G₂).ker := by rw [h1]; exact mem_top _
    exact hg₂ (MonoidHom.mem_ker.1 this)

open CFSG.CGT.Timmesfeld75 in
theorem layerSide_of_conclusion {X : Type} [Group X] [Finite X] {J : Subgroup X} {t : X}
    {k : Type} [Field k] [Finite k] {e : ℕ} (he : 2 ≤ e) (hk : Nat.card k = 2 ^ e)
    (φJ : J ≃* SL(2, k)) (ht2 : orderOf t = 2) (htJ : ∀ j ∈ J, t * j = j * t)
    (hconc : SteinbergBV.OneOrTwoLayerConclusion J t)
    (hred : Nonempty (CFSG.layer X ≃* J × J) ∨ LieModel (CFSG.layer X) .PSL 2 2 (2 * e)) :
    LayerSide X J t e := by
  obtain ⟨-, -, hJl, hnc, -, halt, hfaith'⟩ := hconc
  have h2k : (2 : k) = 0 := by
    haveI := Fintype.ofFinite k
    exact GMSK.two_eq_zero_of_card (n := e) (by omega) (by rw [← Nat.card_eq_fintype_card, hk])
  haveI : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2k
  haveI : Fintype k := Fintype.ofFinite k
  have hk4 : 4 ≤ Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  haveI hJsimple : IsSimpleGroup J := by
    have : IsSimpleGroup (SL(2, k)) := GMSK.sl2_isSimpleGroup h2k hk4
    exact φJ.isSimpleGroup
  have hJnab : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := GMSK.sl2_exists_mul_ne (K := k)
    refine ⟨φJ.symm x, φJ.symm y, fun h => hxy ?_⟩
    simpa using congrArg φJ h
  have hinv : ∃ x : J, x * x = 1 ∧ x ≠ 1 := by
    refine ⟨φJ.symm (utriElt 1), ?_, ?_⟩
    · rw [← map_mul, utriElt_mul_self, map_one]
    · intro h
      have := congrArg φJ h
      rw [MulEquiv.apply_symm_apply, map_one] at this
      exact utriElt_ne_one one_ne_zero this
  have hfaithΛ : ∀ z : X, (∀ d ∈ normalClosure (J : Set X), z * d * z⁻¹ = d) → z = 1 := by
    intro z hz
    refine inv_eq_one.1 (hfaith' z⁻¹ (fun d hd => ?_))
    simpa using hz d hd
  have hJΛ : J ≤ normalClosure (J : Set X) := subset_normalClosure
  have hlayer : CFSG.layer X = normalClosure (J : Set X) := hnc.symm
  rcases halt.or with ⟨hDs, hDna, hJD, hnt⟩ | ⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -, -, ψ, hdiag, hswap⟩
  ·
    rcases hred with ⟨⟨e'⟩⟩ | hL
    · exfalso
      haveI : Nontrivial J := ⟨⟨hinv.choose, 1, hinv.choose_spec.2⟩⟩
      have hs : IsSimpleGroup (CFSG.layer X) := by rw [hlayer]; exact hDs
      exact not_isSimpleGroup_prod' (e'.symm.isSimpleGroup)
    · rcases hL with ⟨-, -, F, hFf, hFfin, hFcard, ⟨eF⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      swap
      · exact absurd h0 (by norm_num)
      swap
      · exact absurd h0 (by norm_num)
      swap
      · exact absurd h0 (by norm_num)
      have hFcard' : Nat.card F = 2 ^ (2 * e) := hFcard
      haveI : CharP F 2 := ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (k := 2 * e) (by omega) hFcard'
      set eSL : CFSG.layer X ≃* SL(2, F) := eF.trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
          CFSG.Walter.psl2MulEquivSL2OfCharTwo) with heSL
      set ι : normalClosure (J : Set X) ≃* SL(2, F) :=
        (MulEquiv.subgroupCongr hlayer).symm.trans eSL with hι
      obtain ⟨hu, hodd, hcl, hcard⟩ := layerSide_simple he hFcard' hk φJ ι hfaithΛ ht2 hJΛ htJ
      refine ⟨hJl, hnc, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hlayer]; exact hfaithΛ
      · rw [hlayer]; exact hu
      · exact hodd
      · rw [hlayer]; exact hcl
      · rw [hlayer]; exact Or.inr hcard
  ·
    obtain ⟨hu, hodd, hcl, hcard⟩ := layerSide_prod hJnab hinv hJΛ hfaithΛ ψ hdiag hswap
    refine ⟨hJl, hnc, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlayer]; exact hfaithΛ
    · rw [hlayer]; exact hu
    · exact hodd
    · rw [hlayer]; exact hcl
    · rw [hlayer]
      left
      rw [hcard, Nat.card_congr φJ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        hk, cardProd]

end Combine



open Subgroup

section Klein

variable {H : Type*} [Group H]

theorem klein_rels (x y : H) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    y * x = x * y ∧ x * (x * y) = y ∧ x * y * x = y ∧ y * (x * y) = x ∧ x * y * y = x ∧
      x * y * (x * y) = 1 := by
  have hyx : y * x = x * y := hxy.symm
  have e1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have e2 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  have e3 : y * (x * y) = x := by rw [← mul_assoc, hyx, mul_assoc, hy, mul_one]
  have e4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have e5 : x * y * (x * y) = 1 := by rw [mul_assoc, e3, hx]
  exact ⟨hyx, e1, e2, e3, e4, e5⟩

@[expose] def kleinSub (x y : H) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Subgroup H where
  carrier := {1, x, y, x * y}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    obtain ⟨hyx, e1, e2, e3, e4, e5⟩ := klein_rels x y hx hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;>
      simp [h, h', hx, hy, e1, e2, e3, e4, e5, hyx]
  inv_mem' := by
    intro a ha
    obtain ⟨hyx, e1, e2, e3, e4, e5⟩ := klein_rels x y hx hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with h | h | h | h
    · left; rw [h]; simp
    · right; left; rw [h]; exact inv_eq_of_mul_eq_one_right hx
    · right; right; left; rw [h]; exact inv_eq_of_mul_eq_one_right hy
    · right; right; right; rw [h]; exact inv_eq_of_mul_eq_one_right e5

theorem mem_kleinSub_iff (x y : H) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    {u : H} : u ∈ kleinSub x y hx hy hxy ↔ u = 1 ∨ u = x ∨ u = y ∨ u = x * y := by
  change u ∈ ({1, x, y, x * y} : Set H) ↔ _
  simp

theorem kleinSub_isElementaryAbelian (x y : H) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : CFSG.IsElementaryAbelian 2 (kleinSub x y hx hy hxy) := by
  obtain ⟨hyx, e1, e2, e3, e4, e5⟩ := klein_rels x y hx hy hxy
  have hcomm : ∀ a b : H, a ∈ kleinSub x y hx hy hxy → b ∈ kleinSub x y hx hy hxy →
      a * b = b * a := by
    intro a b ha hb
    rw [mem_kleinSub_iff] at ha hb
    rcases ha with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;>
      simp [h, h', e1, e2, e3, e4, e5] <;> first | exact hxy | exact hxy.symm
  have hsq : ∀ a : H, a ∈ kleinSub x y hx hy hxy → a * a = 1 := by
    intro a ha
    rw [mem_kleinSub_iff] at ha
    rcases ha with h | h | h | h
    · simp [h]
    · rw [h]; exact hx
    · rw [h]; exact hy
    · rw [h]; exact e5
  exact
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hcomm a b a.2 b.2)⟩⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
        apply Subtype.ext
        have := hsq a a.2
        simpa [pow_two] using this }

end Klein




open Subgroup

section Lift

variable {F : Type*} [Group F] [Finite F]

theorem exists_two_subgroup_lift (R : Subgroup F) [R.Normal] {t : F} (ht : IsPGroup 2 (zpowers t))
    (Q : Subgroup (F ⧸ R)) (hQ : IsPGroup 2 Q) (htQ : QuotientGroup.mk' R t ∈ Q) :
    ∃ P : Subgroup F, IsPGroup 2 P ∧ t ∈ P ∧ P.map (QuotientGroup.mk' R) = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := QuotientGroup.mk' R with hθ
  set Qt : Subgroup F := Q.comap θ with hQt
  have htQt : t ∈ Qt := htQ
  have hz : IsPGroup 2 ((zpowers t).subgroupOf Qt) := ht.comap_subtype
  obtain ⟨S, hS⟩ := hz.exists_le_sylow
  refine ⟨(S : Subgroup Qt).map Qt.subtype, S.isPGroup'.map _, ?_, ?_⟩
  · have : (⟨t, htQt⟩ : Qt) ∈ (zpowers t).subgroupOf Qt := mem_zpowers t
    exact ⟨⟨t, htQt⟩, hS this, rfl⟩
  ·
    let φ : Qt →* Q := ((θ.comp Qt.subtype).codRestrict Q fun x => x.2)
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R (q : F ⧸ R)
      refine ⟨⟨x, by change θ x ∈ Q; rw [hθ, hx]; exact q.2⟩, ?_⟩
      apply Subtype.ext
      exact hx
    have hS' := Sylow.mapSurjective hφ S
    have htop : (Sylow.mapSurjective hφ S : Subgroup Q) = ⊤ := by
      obtain ⟨n, hn⟩ := hQ.index (Sylow.mapSurjective hφ S : Subgroup Q)
      have hnd := (Sylow.mapSurjective hφ S).not_dvd_index
      have hn0 : n = 0 := by
        by_contra hne
        exact hnd (by rw [hn]; exact dvd_pow_self 2 hne)
      rw [hn0, pow_zero] at hn
      exact Subgroup.index_eq_one.1 hn
    ext q
    constructor
    · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
      exact s.2
    · intro hq
      have : (⟨q, hq⟩ : Q) ∈ (Sylow.mapSurjective hφ S : Subgroup Q) := by rw [htop]; exact mem_top _
      rw [Sylow.coe_mapSurjective] at this
      obtain ⟨s, hs, hsq⟩ := this
      refine ⟨(s : F), ⟨s, hs, rfl⟩, ?_⟩
      exact congrArg Subtype.val hsq

end Lift




open Subgroup
open scoped MatrixGroups

open CFSG.LocalAnalysis.EvenBN.GMSK in
theorem sharp_of_input {H : Type} [Group H] [Finite H] {A : Subgroup H} {n : ℕ} (hn : 2 ≤ n)
    {k : Type} [Field k] [Fintype k] (hk : Fintype.card k = 2 ^ n)
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) k) {t : H} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))).Normal) :
    orderOf (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H) t) = 2 ∧
      QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H) t ∈
        centralizer ((A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)) :
          Subgroup (H ⧸ CFSG.Open.standardComponentOddCore H)) :
          Set (H ⧸ CFSG.Open.standardComponentOddCore H)) ∧
      StdLinearData (H ⧸ CFSG.Open.standardComponentOddCore H)
        (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))) n ∧
      SteinbergBV.OneOrTwoLayerConclusion
        (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)))
        (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H) t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.standardComponentOddCore H with hR
  have hAt : A ≤ centralizer ({t} : Set H) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  have hsyl := exists_sylow_inf_centralizer_eq_zpowers ht htA hrank
  have h2 := two_eq_zero_of_card (K := k) (by omega) hk
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    sl2_isSimpleGroup h2 (hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  have : IsSimpleGroup A := φ.isSimpleGroup
  have hnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := k)
    exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩
  have hE : ∃ E : Subgroup H, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
    obtain ⟨E, hE, hE4⟩ := exists_elementaryAbelian_four h2
      (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
    set f : Multiplicative k →* H := A.subtype.comp (φ.symm.toMonoidHom.comp (sl2Upper k))
    have hf : Function.Injective f :=
      A.subtype_injective.comp (φ.symm.injective.comp sl2Upper_injective)
    have hEf : CFSG.IsElementaryAbelian 2 (E.map f) := CFSG.IsElementaryAbelian.map f
    refine ⟨E.map f, ?_, ⟨hEf.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hf, hE4]⟩
    rintro _ ⟨x, -, rfl⟩
    exact (φ.symm (sl2Upper k x)).2
  obtain ⟨hinj, -, hθt, -, -, hAθ, -, -, -, hstd, ⟨S₀, hS₀⟩, -⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE ht hAt hAn hsyl R (odd_card_standardComponentOddCore H)
  have hstdLin : StdLinearData (H ⧸ R) (A.map (QuotientGroup.mk' R)) n := by
    refine ⟨hn, hstd, hnn, k, inferInstance, inferInstance, hk, ⟨?_⟩⟩
    refine (MulEquiv.ofBijective ((QuotientGroup.mk' R).subgroupMap A) ⟨fun x y hxy => ?_,
      (QuotientGroup.mk' R).subgroupMap_surjective A⟩).symm.trans φ
    exact Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
  have htθ : QuotientGroup.mk' R t ∈ centralizer ((A.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) :
      Set (H ⧸ R)) := fun a ha => mem_centralizer_singleton_iff.1 (hAθ ha)
  refine ⟨hθt, htθ, hstdLin, ?_⟩
  have hrel : ¬ 2 ∣ (zpowers (QuotientGroup.mk' R t)).relIndex
      (centralizer ((A.map (QuotientGroup.mk' R) : Subgroup (H ⧸ R)) : Set (H ⧸ R))) := by
    rw [Subgroup.relIndex, ← hS₀, Subgroup.subgroupOf,
      comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    exact S₀.not_dvd_index
  exact oneOrTwoLayer_of_stdLinearData (standardComponentOddCore_quotient_eq_bot H) hstdLin hθt htθ
    hrel



section OddCore

variable {H : Type} [Group H] [Finite H]

theorem eq_of_mk'_eq_of_pgroup (R : Subgroup H) [R.Normal] (hR : Odd (Nat.card R))
    {P : Subgroup H} (hP : IsPGroup 2 P) {x y : H} (hx : x ∈ P) (hy : y ∈ P)
    (hxy : QuotientGroup.mk' R x = QuotientGroup.mk' R y) : x = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : x⁻¹ * y ∈ R := QuotientGroup.eq.1 hxy
  have hzP : x⁻¹ * y ∈ P := mul_mem (inv_mem hx) hy
  have h1 : orderOf (x⁻¹ * y) ∣ Nat.card R := by
    have := orderOf_dvd_natCard (⟨x⁻¹ * y, hz⟩ : R)
    simpa using this
  obtain ⟨k, hk⟩ := hP ⟨x⁻¹ * y, hzP⟩
  have h2 : orderOf (x⁻¹ * y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hk)
  have hcop : Nat.Coprime (Nat.card R) (2 ^ k) := Nat.Coprime.pow_right k hR.coprime_two_right
  have h3 : orderOf (x⁻¹ * y) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : x⁻¹ * y = 1 := orderOf_eq_one_iff.1 h3
  exact inv_mul_eq_one.1 h4


theorem mem_of_involution_mem_map {A : Subgroup H} {t : H} (R : Subgroup H) [R.Normal]
    (hR : Odd (Nat.card R)) [IsSimpleGroup A] (hAeven : Even (Nat.card A))
    (hAt : A ≤ centralizer ({t} : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal) {b : H} (hb2 : b * b = 1)
    (hbt : t * b = b * t)
    (hbA : QuotientGroup.mk' R b ∈ A.map (QuotientGroup.mk' R)) : b ∈ A := by
  obtain ⟨a₀, ha₀, haθ⟩ := hbA
  have hr : a₀⁻¹ * b ∈ R := QuotientGroup.eq.1 haθ
  have hAR : ∀ x ∈ A, x ∈ R → x = 1 := by
    intro x hxA hxR
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf A) with h | h
    · have : (⟨x, hxA⟩ : A) ∈ R.subgroupOf A := hxR
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hAR' : A ≤ R := subgroupOf_eq_top.1 h
      have hdvd : Nat.card A ∣ Nat.card R := Subgroup.card_dvd_of_le hAR'
      exact (Nat.not_even_iff_odd.2 hR) (even_iff_two_dvd.2
        ((even_iff_two_dvd.1 hAeven).trans hdvd))
  have ha₀t : Commute t a₀ := (mem_centralizer_singleton_iff.1 (hAt ha₀)).symm
  set r := a₀⁻¹ * b with hrdef
  have hrt : Commute t r := (ha₀t.inv_right).mul_right hbt
  have hrC : r ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 hrt.symm
  have hconj : r * a₀ * r⁻¹ ∈ A := by
    have h1 : (⟨a₀, hAt ha₀⟩ : centralizer ({t} : Set H)) ∈
        A.subgroupOf (centralizer ({t} : Set H)) := ha₀
    have := hAn.conj_mem _ h1 ⟨r, hrC⟩
    exact this
  have hc : a₀ * r * a₀⁻¹ * r⁻¹ = 1 := by
    apply hAR
    · have e : a₀ * r * a₀⁻¹ * r⁻¹ = a₀ * (r * a₀ * r⁻¹)⁻¹ := by group
      rw [e]
      exact mul_mem ha₀ (inv_mem hconj)
    · exact mul_mem (Normal.conj_mem inferInstance r hr a₀) (inv_mem hr)
  have hcomm : a₀ * r = r * a₀ := by
    have : a₀ * r = a₀ * r * a₀⁻¹ * r⁻¹ * (r * a₀) := by group
    rw [this, hc, one_mul]
  have hb : b = a₀ * r := by rw [hrdef]; group
  have hsq : a₀ * a₀ * (r * r) = 1 := by
    have := hb2
    rw [hb] at this
    calc a₀ * a₀ * (r * r) = a₀ * (a₀ * r) * r := by group
      _ = a₀ * (r * a₀) * r := by rw [hcomm]
      _ = a₀ * r * (a₀ * r) := by group
      _ = 1 := this
  have ha2 : a₀ * a₀ = 1 := by
    apply hAR
    · exact mul_mem ha₀ ha₀
    · have : a₀ * a₀ = (r * r)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact inv_mem (mul_mem hr hr)
  have hr2 : r * r = 1 := by rw [ha2, one_mul] at hsq; exact hsq
  have hr1 : r = 1 := by
    have h1 : orderOf r ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨r, hr⟩ : R)
      simpa using this
    have h2 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hr2)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hR.coprime_two_right h1 h2)
  rw [hb, hr1, mul_one]
  exact ha₀


open CFSG.LocalAnalysis.ComponentInitial in
theorem odd_core_commutes_of_layer {A : Subgroup H} {t : H} (R : Subgroup H) [R.Normal]
    (hR : Odd (Nat.card R)) [IsSimpleGroup A] (hAnab : ∃ x y : A, x * y ≠ y * x)
    (hAeven : Even (Nat.card A)) (ht2 : orderOf t = 2) (hAt : A ≤ centralizer ({t} : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal) {u v : H ⧸ R} (hu2 : u * u = 1)
    (hv : v = (QuotientGroup.mk' R t)⁻¹ * u * QuotientGroup.mk' R t) (huv : u * v = v * u)
    (hne : u * v ≠ 1) (hA : u * v ∈ A.map (QuotientGroup.mk' R)) :
    Group.IsPerfect (normalClosure (A : Set H)) ∧
      ∀ A' : Subgroup H, A'.Normal → Odd (Nat.card A') → ⁅A', normalClosure (A : Set H)⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := QuotientGroup.mk' R with hθ
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hθt2 : θ t * θ t = 1 := by rw [← map_mul, htt, map_one]
  have hθtinv : (θ t)⁻¹ = θ t := inv_eq_of_mul_eq_one_right hθt2
  rw [hθtinv] at hv
  have hv2 : v * v = 1 := by
    rw [hv]
    calc θ t * u * θ t * (θ t * u * θ t) = θ t * (u * (θ t * θ t) * u) * θ t := by group
      _ = 1 := by rw [hθt2, mul_one, hu2, mul_one, hθt2]
  set Ub := kleinSub u v hu2 hv2 huv with hUb
  haveI hUbE : CFSG.IsElementaryAbelian 2 Ub := kleinSub_isElementaryAbelian u v hu2 hv2 huv
  have hUb2 : IsPGroup 2 Ub := CFSG.IsElementaryAbelian.isPGroup 2 Ub
  have htz : IsPGroup 2 (zpowers (θ t)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    have : orderOf (θ t) ∣ orderOf t := orderOf_map_dvd θ t
    rw [ht2] at this
    simpa using this
  have htz' : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht2, pow_one]
  have hnorm : zpowers (θ t) ≤ normalizer (Ub : Set (H ⧸ R)) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, hUb, mem_kleinSub_iff] at hx ⊢
    have e1 : θ t * u * (θ t)⁻¹ = v := by rw [hv, hθtinv]
    have e2 : θ t * v * (θ t)⁻¹ = u := by
      rw [hv, hθtinv]
      calc θ t * (θ t * u * θ t) * θ t = (θ t * θ t) * u * (θ t * θ t) := by group
        _ = u := by rw [hθt2]; simp
    rcases hx with h | h | h | h <;> rw [h]
    · left; simp
    · right; right; left; exact e1
    · right; left; exact e2
    · right; right; right
      calc θ t * (u * v) * (θ t)⁻¹ = (θ t * u * (θ t)⁻¹) * (θ t * v * (θ t)⁻¹) := by group
        _ = v * u := by rw [e1, e2]
        _ = u * v := huv.symm
  set Q := zpowers (θ t) ⊔ Ub with hQdef
  have hQ : IsPGroup 2 Q := htz.to_sup_of_normal_right' hUb2 hnorm
  have htQ : θ t ∈ Q := mem_sup_left (mem_zpowers _)
  obtain ⟨P, hP2, htP, hPQ⟩ := exists_two_subgroup_lift R htz' Q hQ htQ
  have hinjP : ∀ x ∈ P, ∀ y ∈ P, θ x = θ y → x = y := fun x hx y hy h =>
    eq_of_mk'_eq_of_pgroup R hR hP2 hx hy h
  have huUb : u ∈ Ub := by
    rw [hUb, mem_kleinSub_iff]
    right; left; rfl
  have huQ : u ∈ Q := mem_sup_right huUb
  obtain ⟨u1, hu1P, hu1θ⟩ : ∃ u1 ∈ P, θ u1 = u := by
    rw [← hPQ] at huQ
    exact huQ
  obtain ⟨v1, hv1def⟩ : ∃ v1 : H, v1 = t * u1 * t := ⟨_, rfl⟩
  have hv1P : v1 ∈ P := by rw [hv1def]; exact mul_mem (mul_mem htP hu1P) htP
  have hv1θ : θ v1 = v := by rw [hv1def, map_mul, map_mul, hu1θ, hv]
  have hu12 : u1 * u1 = 1 :=
    hinjP _ (mul_mem hu1P hu1P) _ (one_mem _) (by rw [map_mul, hu1θ, hu2, map_one])
  have hv12 : v1 * v1 = 1 :=
    hinjP _ (mul_mem hv1P hv1P) _ (one_mem _) (by rw [map_mul, hv1θ, hv2, map_one])
  have hu1v1 : u1 * v1 = v1 * u1 :=
    hinjP _ (mul_mem hu1P hv1P) _ (mul_mem hv1P hu1P) (by rw [map_mul, map_mul, hu1θ, hv1θ, huv])
  obtain ⟨b, hbdef⟩ : ∃ b : H, b = u1 * v1 := ⟨_, rfl⟩
  have hbP : b ∈ P := by rw [hbdef]; exact mul_mem hu1P hv1P
  have hθb : θ b = u * v := by rw [hbdef, map_mul, hu1θ, hv1θ]
  have hb1 : b ≠ 1 := fun h => hne (by rw [← hθb, h, map_one])
  have hu1inv : u1⁻¹ = u1 := inv_eq_of_mul_eq_one_right hu12
  have hv1inv : v1⁻¹ = v1 := inv_eq_of_mul_eq_one_right hv12
  have hb2 : b * b = 1 := by
    rw [hbdef]
    calc u1 * v1 * (u1 * v1) = u1 * (v1 * u1) * v1 := by group
      _ = u1 * (u1 * v1) * v1 := by rw [← hu1v1]
      _ = u1 * u1 * (v1 * v1) := by group
      _ = 1 := by rw [hu12, hv12, mul_one]
  have hbt : t * b = b * t := by
    rw [hbdef]
    calc t * (u1 * v1) = (t * u1 * t) * u1 * t := by
          rw [hv1def]; group
      _ = v1 * u1 * t := by rw [← hv1def]
      _ = u1 * v1 * t := by rw [← hu1v1]
  have hbA : b ∈ A :=
    mem_of_involution_mem_map R hR hAeven hAt hAn hb2 hbt (by rw [hθb]; exact hA)
  haveI hUE : CFSG.IsElementaryAbelian 2 (kleinSub u1 v1 hu12 hv12 hu1v1) :=
    kleinSub_isElementaryAbelian u1 v1 hu12 hv12 hu1v1
  have hv1t : t * v1 * t = u1 := by
    rw [hv1def]
    calc t * (t * u1 * t) * t = (t * t) * u1 * (t * t) := by group
      _ = u1 := by rw [htt]; simp
  have htu1 : t * u1 * t = v1 := hv1def.symm
  have hbtt : t * (u1 * v1) * t = u1 * v1 := by
    have := hbt
    rw [hbdef] at this
    rw [this, mul_assoc, htt, mul_one]
  have haU : t ∈ normalizer ((kleinSub u1 v1 hu12 hv12 hu1v1 : Subgroup H) : Set H) := by
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, mem_kleinSub_iff] at hx ⊢
    rw [htinv]
    rcases hx with h | h | h | h <;> rw [h]
    · left; rw [mul_one]; exact htt
    · right; right; left; exact htu1
    · right; left; exact hv1t
    · right; right; right; exact hbtt
  have hgen : ∀ x ∈ {x | ∃ w ∈ (kleinSub u1 v1 hu12 hv12 hu1v1 : Subgroup H),
      x = w⁻¹ * (t⁻¹ * w * t)}, x = 1 ∨ x = b := by
    rintro x ⟨w, hw, rfl⟩
    rw [mem_kleinSub_iff] at hw
    rw [htinv]
    rcases hw with h | h | h | h <;> rw [h]
    · left; rw [inv_one, one_mul, mul_one]; exact htt
    · right; rw [htu1, hu1inv, ← hbdef]
    · right; rw [hv1t, hv1inv, ← hu1v1, ← hbdef]
    · left; rw [hbtt, inv_mul_cancel]
  have hBJ : closure {x | ∃ w ∈ (kleinSub u1 v1 hu12 hv12 hu1v1 : Subgroup H),
      x = w⁻¹ * (t⁻¹ * w * t)} ≤ A := by
    rw [closure_le]
    intro x hx
    rcases hgen x hx with h | h <;> rw [h]
    exacts [one_mem _, hbA]
  have hB : closure {x | ∃ w ∈ (kleinSub u1 v1 hu12 hv12 hu1v1 : Subgroup H),
      x = w⁻¹ * (t⁻¹ * w * t)} ≠ ⊥ := by
    intro h
    have hbmem : b ∈ closure {x | ∃ w ∈ (kleinSub u1 v1 hu12 hv12 hu1v1 : Subgroup H),
        x = w⁻¹ * (t⁻¹ * w * t)} :=
      subset_closure ⟨u1, by rw [mem_kleinSub_iff]; right; left; rfl,
        by rw [htinv, htu1, hu1inv, ← hbdef]⟩
    rw [h, mem_bot] at hbmem
    exact hb1 hbmem
  have hT := elementary_involution_commutator_centralizes_odd_normal_core ht2 hAnab hAt hAn haU hB
    hBJ (L := normalClosure (A : Set H)) rfl
  exact ⟨hT.1, hT.2.1⟩

end OddCore


section HData

variable {H : Type} [Group H] [Finite H]

structure HData (H : Type) [Group H] [Finite H] (A : Subgroup H) (e : ℕ) : Prop where
  perfect : ⁅normalClosure (A : Set H), normalClosure (A : Set H)⁆ = normalClosure (A : Set H)
  comm : ∀ x ∈ CFSG.Open.standardComponentOddCore H, ∀ y ∈ normalClosure (A : Set H),
    x * y = y * x
  centralizer_le : ∀ x : H, (∀ y ∈ normalClosure (A : Set H), x * y = y * x) →
    x ∈ CFSG.Open.standardComponentOddCore H
  odd_centralizer : ∀ z : H, (∀ a ∈ A, z * a = a * z) → Odd (orderOf z) →
    z ∈ CFSG.Open.standardComponentOddCore H
  closure_in : ∀ N : Subgroup H, A ≤ N → N ≤ normalClosure (A : Set H) →
    (∀ g ∈ normalClosure (A : Set H), ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
    ∀ x ∈ normalClosure (A : Set H), ∃ n ∈ N, n⁻¹ * x ∈ CFSG.Open.standardComponentOddCore H
  map_eq : (normalClosure (A : Set H)).map
      (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)) =
    CFSG.layer (H ⧸ CFSG.Open.standardComponentOddCore H)
  card : Nat.card ((normalClosure (A : Set H)).map
      (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))) = cardProd e ∨
    Nat.card ((normalClosure (A : Set H)).map
      (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))) = cardSimple e

open CFSG.LocalAnalysis.EvenBN.GMSK in
theorem hdata_of_input {A : Subgroup H} {t : H} {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k]
    [Fintype k] (hk : Fintype.card k = 2 ^ n) (φ : A ≃* SL(2, k)) (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set H))
    (hAn : (A.subgroupOf (centralizer ({t} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ (A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))).Normal)
    (hred : Nonempty (CFSG.layer (H ⧸ CFSG.Open.standardComponentOddCore H) ≃*
        ↥(A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))) ×
        ↥(A.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H)))) ∨
      LieModel (CFSG.layer (H ⧸ CFSG.Open.standardComponentOddCore H)) .PSL 2 2 (2 * n)) :
    HData H A n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.standardComponentOddCore H with hO
  set θ := QuotientGroup.mk' O with hθ
  have hOodd : Odd (Nat.card O) := odd_card_standardComponentOddCore H
  obtain ⟨hθt2, hθtc, hstd, hconc⟩ := sharp_of_input hn hk φ ht htA hAn hrank hnn
  obtain ⟨-, -, -, k', hk'F, hk'fin, hk'card, ⟨φ'⟩⟩ := hstd
  have htJ : ∀ j ∈ A.map θ, θ t * j = j * θ t := fun j hj =>
    (mem_centralizer_iff.1 hθtc j hj).symm
  have hside : LayerSide (H ⧸ O) (A.map θ) (θ t) n :=
    layerSide_of_conclusion hn (by rw [Nat.card_eq_fintype_card]; exact hk'card) φ' hθt2 htJ hconc
      hred
  have h2 : (2 : k) = 0 := two_eq_zero_of_card (by omega) hk
  have hk4 : 4 ≤ Fintype.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : IsSimpleGroup (SL(2, k)) := sl2_isSimpleGroup h2 hk4
  haveI : IsSimpleGroup A := φ.isSimpleGroup
  have hAnab : ∃ x y : A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := k)
    exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩
  have hAeven : Even (Nat.card A) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_eq_fintype_card, hk]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
  have hAt : A ≤ centralizer ({t} : Set H) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  obtain ⟨u, huΛ, hu2ord, huv, hne, huA⟩ := hside.exists_u
  have hu2 : u * u = 1 := by
    rw [← pow_two, ← hu2ord]
    exact pow_orderOf_eq_one u
  obtain ⟨hperf, hodd⟩ := odd_core_commutes_of_layer O hOodd hAnab hAeven ht hAt hAn hu2 rfl huv
    hne huA
  have hθsurj : Function.Surjective θ := QuotientGroup.mk'_surjective O
  have hθL : (normalClosure (A : Set H)).map θ = CFSG.layer (H ⧸ O) := by
    rw [Subgroup.map_normalClosure _ θ hθsurj, ← hside.closure_eq]
    congr 1
  refine ⟨Subgroup.isPerfect_iff.1 hperf, ?_, ?_, ?_, ?_, hθL, ?_⟩
  · intro x hx y hy
    have := hodd O inferInstance hOodd
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at this
    exact (mem_centralizer_iff.1 (this hx) y hy).symm
  · intro x hx
    have : θ x = 1 := by
      refine hside.faithful (θ x) fun d hd => ?_
      rw [← hθL] at hd
      obtain ⟨y, hy, rfl⟩ := hd
      have := hx y hy
      calc θ x * θ y * (θ x)⁻¹ = θ (x * y * x⁻¹) := by simp
        _ = θ y := by rw [this]; simp
    exact (QuotientGroup.eq_one_iff x).1 this
  · intro z hz hzodd
    have : θ z = 1 := by
      refine hside.odd_centralizer (θ z) (fun j hj => ?_) ?_
      · obtain ⟨a, ha, rfl⟩ := hj
        calc θ z * θ a = θ (z * a) := by simp
          _ = θ (a * z) := by rw [hz a ha]
          _ = θ a * θ z := by simp
      · exact hzodd.of_dvd_nat (orderOf_map_dvd θ z)
    exact (QuotientGroup.eq_one_iff z).1 this
  · intro N hAN hNL hNinv x hx
    have hθN : (N.map θ) = CFSG.layer (H ⧸ O) := by
      refine hside.closure_in (N.map θ) (map_mono hAN) ?_ ?_
      · rw [← hθL]; exact map_mono hNL
      · rintro g hg _ ⟨n, hn, rfl⟩
        rw [← hθL] at hg
        obtain ⟨g', hg', rfl⟩ := hg
        exact ⟨g' * n * g'⁻¹, hNinv g' hg' n hn, by simp⟩
    have hxΛ : θ x ∈ N.map θ := by rw [hθN, ← hθL]; exact ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hnx⟩ := hxΛ
    refine ⟨n, hn, ?_⟩
    have : n⁻¹ * x ∈ O := by
      rw [← QuotientGroup.eq]
      exact hnx
    exact this
  · rw [hθL]
    exact hside.card

end HData


theorem commutatorElement_mul_mul_of_commute {G' : Type*} [Group G'] {n₁ n₂ w₁ w₂ : G'}
    (h1 : Commute w₁ n₁) (h2 : Commute w₁ n₂) (h3 : Commute w₁ w₂) (h4 : Commute w₂ n₁)
    (h5 : Commute w₂ n₂) : ⁅n₁ * w₁, n₂ * w₂⁆ = ⁅n₁, n₂⁆ := by
  have a1 : Commute w₁⁻¹ n₁ := h1.inv_left
  have a2 : Commute w₁⁻¹ n₂ := h2.inv_left
  have a3 : Commute w₁⁻¹ w₂ := h3.inv_left
  have a4 : Commute w₂⁻¹ n₁ := h4.inv_left
  have a5 : Commute w₂⁻¹ n₂ := h5.inv_left
  have a6 : Commute w₁ w₂⁻¹ := h3.inv_right
  have a7 : Commute w₁ n₂⁻¹ := h2.inv_right
  have a8 : Commute w₂ n₂⁻¹ := h5.inv_right
  have a9 : Commute w₂ n₁⁻¹ := h4.inv_right
  have a10 : Commute w₁ n₁⁻¹ := h1.inv_right
  have hZ : Commute w₁ (n₂ * w₂) := h2.mul_right h3
  have e1 : w₁ * (n₂ * w₂) * w₁⁻¹ = n₂ * w₂ := by rw [hZ.eq, mul_inv_cancel_right]
  have e2 : w₂ * n₁⁻¹ * w₂⁻¹ = n₁⁻¹ := by rw [a9.eq, mul_inv_cancel_right]
  calc ⁅n₁ * w₁, n₂ * w₂⁆ = n₁ * (w₁ * (n₂ * w₂) * w₁⁻¹) * n₁⁻¹ * w₂⁻¹ * n₂⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = n₁ * (n₂ * w₂) * n₁⁻¹ * w₂⁻¹ * n₂⁻¹ := by rw [e1]
    _ = n₁ * n₂ * (w₂ * n₁⁻¹ * w₂⁻¹) * n₂⁻¹ := by simp only [mul_assoc]
    _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by rw [e2]
    _ = ⁅n₁, n₂⁆ := by simp only [commutatorElement_def]


section LayerEq

variable {H : Type} [Group H] [Finite H]

theorem le_of_perfect_of_factor {L N : Subgroup H} (hperf : ⁅L, L⁆ = L) (hNL : N ≤ L)
    (hfac : ∀ x ∈ L, ∃ n ∈ N, ∀ y ∈ L, (n⁻¹ * x) * y = y * (n⁻¹ * x)) : L ≤ N := by
  rw [← hperf]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨n₁, hn₁, hw₁⟩ := hfac x hx
  obtain ⟨n₂, hn₂, hw₂⟩ := hfac y hy
  obtain ⟨w₁, hw₁def⟩ : ∃ w₁ : H, w₁ = n₁⁻¹ * x := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂def⟩ : ∃ w₂ : H, w₂ = n₂⁻¹ * y := ⟨_, rfl⟩
  rw [← hw₁def] at hw₁
  rw [← hw₂def] at hw₂
  have hx' : x = n₁ * w₁ := by rw [hw₁def]; group
  have hy' : y = n₂ * w₂ := by rw [hw₂def]; group
  have hn₁L : n₁ ∈ L := hNL hn₁
  have hn₂L : n₂ ∈ L := hNL hn₂
  have hw₁L : w₁ ∈ L := by rw [hw₁def]; exact mul_mem (inv_mem hn₁L) hx
  have hw₂L : w₂ ∈ L := by rw [hw₂def]; exact mul_mem (inv_mem hn₂L) hy
  have key : ⁅x, y⁆ = ⁅n₁, n₂⁆ := by
    rw [hx', hy']
    exact commutatorElement_mul_mul_of_commute (hw₁ n₁ hn₁L) (hw₁ n₂ hn₂L) (hw₁ w₂ hw₂L)
      (hw₂ n₁ hn₁L) (hw₂ n₂ hn₂L)
  rw [key, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

theorem le_of_perfect_of_mem_sup_odd {L M O : Subgroup H} [L.Normal] (hM : ⁅M, M⁆ = M)
    (hO : Odd (Nat.card O)) (hMLO : ∀ m ∈ M, ∃ x ∈ L, x⁻¹ * m ∈ O) : M ≤ L := by
  set q := QuotientGroup.mk' L with hq
  set K := M.map q with hK
  have hKperf : ⁅K, K⁆ = K := by rw [hK, ← Subgroup.map_commutator, hM]
  have hKO : K ≤ O.map q := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨x, hxL, hxO⟩ := hMLO m hm
    refine ⟨x⁻¹ * m, hxO, ?_⟩
    simp only [hq, map_mul, map_inv]
    have : QuotientGroup.mk' L x = 1 := (QuotientGroup.eq_one_iff x).2 hxL
    rw [this]; simp
  have hKodd : Odd (Nat.card K) := by
    have h1 : Nat.card K ∣ Nat.card (O.map q) := Subgroup.card_dvd_of_le hKO
    have h2 : Nat.card (O.map q) ∣ Nat.card O := Subgroup.card_map_dvd (H := O) q
    exact (hO.of_dvd_nat (h1.trans h2))
  haveI : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd
  haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hKperf
  have hKbot : K = ⊥ := by
    by_contra hne
    haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
    exact Group.IsPerfect.not_isSolvable K inferInstance
  intro m hm
  have : q m ∈ K := ⟨m, hm, rfl⟩
  rw [hKbot, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff m).1 this

end LayerEq

section BarPerfect

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_perfect {X K : Subgroup G} (hK : ⁅K, K⁆ = K) (hKX : K ≤ X) :
    ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKX, hK]

theorem bar_perfect {D K : Subgroup G} (hK : ⁅K, K⁆ = K) (hKN : K ≤ normalizer (D : Set G)) :
    ⁅bar D K, bar D K⁆ = bar D K := by
  unfold bar
  rw [← Subgroup.map_commutator, subgroupOf_perfect hK hKN]

end BarPerfect

end S3e

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec39_layer (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hin : d.Sec39Input) (hnn : d.Sec39NotNormal) (ho : d.Sec39Outcome)
    (hr : d.Sec39Reduced) : d.Sec39Layer := by
  obtain ⟨kf, _, _, hkf, ⟨φ⟩⟩ := hin.field
  have h2 := hp.hyp.two_le
  have hdata : S3e.HData (Bar d.D) (bar d.D d.N₁) (2 * f) :=
    S3e.hdata_of_input (by omega) hkf φ hin.order_two hin.centralizes hin.normal hin.rank hnn
      hr.layer_type
  have hN₁perf : ⁅d.N₁, d.N₁⁆ = d.N₁ := by
    unfold Data.N₁ Data.pull
    rw [← Subgroup.map_commutator, commutator_N₁sub]
  have hM₁perf : ⁅d.M₁, d.M₁⁆ = d.M₁ :=
    commutator_normalClosureIn d.N₁_le_centralizer_I₁ hN₁perf
  have hMperf : ⁅bar d.D d.M₁, bar d.D d.M₁⁆ = bar d.D d.M₁ :=
    S3e.bar_perfect hM₁perf hr.M₁_le
  set θ := QuotientGroup.mk' (OD d) with hθ
  have hMθ : (bar d.D d.M₁).map θ = CFSG.layer (Bar d.D ⧸ OD d) := hr.map_eq
  have hLθ : (normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D))).map θ =
      CFSG.layer (Bar d.D ⧸ OD d) := hdata.map_eq
  have hMLO : ∀ m ∈ bar d.D d.M₁, ∃ x ∈ normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) :
      Set (Bar d.D)), x⁻¹ * m ∈ OD d := by
    intro m hm
    have : θ m ∈ (normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D))).map θ := by
      rw [hLθ, ← hMθ]; exact ⟨m, hm, rfl⟩
    obtain ⟨x, hx, hxm⟩ := this
    exact ⟨x, hx, QuotientGroup.eq.1 hxm⟩
  have hML : bar d.D d.M₁ ≤ normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) :=
    S3e.le_of_perfect_of_mem_sup_odd hMperf (GMSK.odd_card_standardComponentOddCore _) hMLO
  have hfac : ∀ x ∈ normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)),
      ∃ n ∈ bar d.D d.M₁, ∀ y ∈ normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) :
        Set (Bar d.D)), (n⁻¹ * x) * y = y * (n⁻¹ * x) := by
    intro x hx
    have : θ x ∈ (bar d.D d.M₁).map θ := by
      rw [hMθ, ← hLθ]; exact ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hnx⟩ := this
    exact ⟨n, hn, fun y hy => hdata.comm _ (QuotientGroup.eq.1 hnx) y hy⟩
  have hLM : normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) ≤
      bar d.D d.M₁ := S3e.le_of_perfect_of_factor hdata.perfect hML hfac
  have heq : normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) =
      bar d.D d.M₁ := le_antisymm hLM hML
  refine ⟨heq, ?_⟩
  ext x
  rw [mem_centralizer_iff]
  constructor
  · intro hx
    refine hdata.centralizer_le x fun y hy => ?_
    exact (hx y (heq ▸ hy)).symm
  · intro hx y hy
    exact (hdata.comm x hx y (heq ▸ hy)).symm

end Data

namespace CaseBParts

theorem sec39Layer : Sec39LayerStatement :=
  fun _ _ _ _ _ _ _ _ hp k he hin hnn ho hr => Data.sec39_layer hp k he hin hnn ho hr

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
