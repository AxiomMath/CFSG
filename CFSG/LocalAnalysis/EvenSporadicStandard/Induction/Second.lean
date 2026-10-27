module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {G : Type} [Group G]

theorem exists_hom_of_sq_eq_one {Λ : Type*} [Group Λ] (τ : Λ) (h : τ * τ = 1) :
    ∃ g : Multiplicative (ZMod 2) →* Λ, g (Multiplicative.ofAdd 1) = τ := by
  have h2 : (zmultiplesHom (Additive Λ) (Additive.ofMul τ)) ((2 : ℕ) : ℤ) = 0 := by
    simp only [zmultiplesHom_apply]
    show ((2 : ℕ) : ℤ) • Additive.ofMul τ = 0
    rw [natCast_zsmul]
    show Additive.ofMul (τ ^ 2) = Additive.ofMul 1
    rw [pow_two, h]
  refine ⟨AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift 2 ⟨zmultiplesHom (Additive Λ) (Additive.ofMul τ), h2⟩), ?_⟩
  rw [AddMonoidHom.coe_toMultiplicativeLeft]
  have h3 := ZMod.lift_coe 2 ⟨zmultiplesHom (Additive Λ) (Additive.ofMul τ), h2⟩ (1 : ℤ)
  have h4 : ((1 : ℤ) : ZMod 2) = 1 := Int.cast_one
  rw [h4] at h3
  show Additive.toMul ((ZMod.lift 2 ⟨zmultiplesHom (Additive Λ) (Additive.ofMul τ), h2⟩) 1) = τ
  rw [h3]
  simp

theorem false_of_second_copy_emb {L K N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (htK : t ∈ centralizer (K : Set G)) (hKq : CFSG.IsQuasisimple ↥K)
    (hΛs : Group.IsSolvable ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)))
    (hemb : NoFixedEmbeds ↥K ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)))
    (hN : N ≤ centralizer (K : Set G)) (e : N ≃* K) (htN : t ∈ normalizer (N : Set G)) :
    False := by
  have hΛ : ∀ n ∈ N, t * n * t⁻¹ = n →
      n ∈ normalizer (L : Set G) ⊓ centralizer (K : Set G) := by
    intro n hn hnt
    refine ⟨hCt (mem_centralizer_singleton_iff.2 ?_), hN hn⟩
    calc n * t = (t * n * t⁻¹) * t := by rw [hnt]
      _ = t * n := by group
  have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq
  by_cases hall : ∀ n ∈ N, t * n * t⁻¹ = n
  · have hNΛ : N ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) := fun n hn =>
      hΛ n hn (hall n hn)
    have hsolv : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNΛ)
        (Subgroup.inclusion_injective hNΛ)
    have := CFSG.LocalCores.isQuasisimple_nontrivial hNq
    have : Group.IsPerfect ↥N := hNq.1
    exact Group.IsPerfect.not_isSolvable ↥N hsolv
  · push Not at hall
    obtain ⟨n₀, hn₀, hn₀t⟩ := hall
    set α : MulAut ↥N := Subgroup.normalizerMonoidHom N ⟨t, htN⟩ with hα
    have hαapp : ∀ n : ↥N, ((α n : ↥N) : G) = t * n * t⁻¹ := fun n =>
      Subgroup.normalizerMonoidHom_apply_apply_coe N ⟨t, htN⟩ n
    set α' : MulAut ↥K := MulAut.congr e α with hα'
    have hα1 : α ≠ 1 := by
      intro h1
      apply hn₀t
      have := hαapp ⟨n₀, hn₀⟩
      rw [h1] at this
      exact this.symm
    have hα'1 : α' ≠ 1 := by
      intro h1
      apply hα1
      apply (MulAut.congr e).injective
      rw [← hα', h1, map_one]
    have hαα : α * α = 1 := by
      have : (⟨t, htN⟩ : ↥(normalizer (N : Set G))) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
      rw [hα, ← map_mul, this, map_one]
    have hα'α' : α' * α' = 1 := by
      rw [hα', ← map_mul, hαα, map_one]
    have hfix : ∀ k : ↥(fixSubgroup α'),
        t * ((e.symm (k : ↥K) : ↥N) : G) * t⁻¹ = ((e.symm (k : ↥K) : ↥N) : G) := by
      intro k
      have h1 : α (e.symm (k : ↥K)) = e.symm (k : ↥K) := by
        have h2 : ∀ kk : ↥K, α' kk = e (α (e.symm kk)) := fun kk => by
          rw [hα', MulAut.congr_apply]
          rfl
        have h3 : α' (k : ↥K) = (k : ↥K) := k.2
        rw [h2 (k : ↥K)] at h3
        exact e.injective (by simpa using h3)
      rw [← hαapp, h1]
    let f : ↥(fixSubgroup α') →* ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)) :=
      { toFun := fun k => ⟨((e.symm (k : ↥K) : ↥N) : G),
          hΛ _ (e.symm (k : ↥K)).2 (hfix k)⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp }
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : ((e.symm (a : ↥K) : ↥N) : G) = ((e.symm (b : ↥K) : ↥N) : G) :=
        congrArg (fun z : ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)) => (z : G)) hab
      have h2 : e.symm (a : ↥K) = e.symm (b : ↥K) := Subtype.ext h1
      exact Subtype.ext (e.symm.injective h2)
    by_cases htNm : t ∈ N
    ·
      have hinner : ∃ k : ↥K, α' = MulAut.conj k := by
        refine ⟨e ⟨t, htNm⟩, ?_⟩
        have hαc : α = MulAut.conj (⟨t, htNm⟩ : ↥N) := by
          ext n
          rw [hαapp]
          simp [MulAut.conj_apply]
        rw [hα', hαc]
        ext k
        simp [MulAut.congr_apply, MulAut.conj_apply]
      exact ((hemb α' hα'1 hα'α').2 hinner) ⟨f, hf⟩
    ·
      have htΛ : t ∈ normalizer (L : Set G) ⊓ centralizer (K : Set G) :=
        ⟨hCt (mem_centralizer_singleton_iff.2 rfl), htK⟩
      obtain ⟨g, hg⟩ := exists_hom_of_sq_eq_one
        (⟨t, htΛ⟩ : ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G))) (Subtype.ext ht2)
      have hb2 : ∀ b : Multiplicative (ZMod 2), b = 1 ∨ b = Multiplicative.ofAdd 1 := by
        intro b
        have : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        rcases this (Multiplicative.toAdd b) with h0 | h1
        · exact Or.inl (by simpa using congrArg Multiplicative.ofAdd h0)
        · exact Or.inr (by simpa using congrArg Multiplicative.ofAdd h1)
      have hg1 : g 1 = 1 := map_one g
      have hcomm : ∀ (a : ↥(fixSubgroup α')) (b : Multiplicative (ZMod 2)),
          Commute (f a) (g b) := by
        intro a b
        rcases hb2 b with rfl | rfl
        · rw [hg1]
          exact Commute.one_right _
        · rw [hg]
          refine Subtype.ext ?_
          show ((e.symm (a : ↥K) : ↥N) : G) * t = t * ((e.symm (a : ↥K) : ↥N) : G)
          have := hfix a
          calc ((e.symm (a : ↥K) : ↥N) : G) * t
              = (t * ((e.symm (a : ↥K) : ↥N) : G) * t⁻¹) * t := by rw [this]
            _ = t * ((e.symm (a : ↥K) : ↥N) : G) := by group
      have hcoe : ∀ x : ↥(fixSubgroup α'),
          ((f x : ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G))) : G) =
            ((e.symm (x : ↥K) : ↥N) : G) := fun x => rfl
      have hne : ∀ x y : ↥(fixSubgroup α'), f x * ⟨t, htΛ⟩ ≠ f y := by
        intro x y hxy
        apply htNm
        have h1 := congrArg (fun z : ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)) =>
          (z : G)) hxy
        simp only [Subgroup.coe_mul, hcoe] at h1
        have h2 : t = (((e.symm (x : ↥K) : ↥N) : G))⁻¹ * ((e.symm (y : ↥K) : ↥N) : G) := by
          calc t = (((e.symm (x : ↥K) : ↥N) : G))⁻¹ *
                (((e.symm (x : ↥K) : ↥N) : G) * t) := by group
            _ = _ := by rw [h1]
        rw [h2]
        exact N.mul_mem (N.inv_mem (e.symm (x : ↥K)).2) (e.symm (y : ↥K)).2
      refine (hemb α' hα'1 hα'α').1 ⟨f.noncommCoprod g hcomm, ?_⟩
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have hab' : f a * g b = f a' * g b' := by
        simpa [MonoidHom.noncommCoprod_apply] using hab
      rcases hb2 b with rfl | rfl <;> rcases hb2 b' with rfl | rfl
      · rw [hg1, mul_one, mul_one] at hab'
        exact Prod.ext (hf hab') rfl
      · rw [hg1, hg, mul_one] at hab'
        exact (hne a' a hab'.symm).elim
      · rw [hg1, hg, mul_one] at hab'
        exact (hne a a' hab').elim
      · rw [hg, mul_left_inj] at hab'
        exact Prod.ext (hf hab') rfl

theorem normal_of_component_emb [Finite G] {L K X : Subgroup G} {t : G}
    (hK : IsCompIn K X) (htX : t ∈ X) (htK : t ∈ centralizer (K : Set G)) (ht2 : t * t = 1)
    (hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hΛs : Group.IsSolvable ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G)))
    (hemb : NoFixedEmbeds ↥K ↥(normalizer (L : Set G) ⊓ centralizer (K : Set G))) :
    (K.subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK.1]
  intro h hh
  have hKq := hK.isQuasisimple
  rw [CFSG.EvenSporadicStandard.Solomon78.mem_normalizer_iff_map_conj_eq]
  by_contra hNK
  set N : Subgroup G := K.map (MulAut.conj h).toMonoidHom with hNdef
  have hNcomp : IsCompIn N X := hK.map_conj hh
  have hcardN : Nat.card N = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hNcentK : ∀ a ∈ N, ∀ b ∈ K, b * a = a * b := fun a ha b hb =>
    (hNcomp.commute_of_ne hK hNK a ha b hb).symm
  by_cases htN : t ∈ normalizer (N : Set G)
  · exact false_of_second_copy_emb ht2 hCt htK hKq hΛs hemb
      (fun a ha => mem_centralizer_iff.2 (hNcentK a ha))
      (Subgroup.equivMapOfInjective K (MulAut.conj h).toMonoidHom (MulAut.conj h).injective).symm
      htN
  ·
    set N' : Subgroup G := N.map (MulAut.conj t).toMonoidHom with hN'def
    have hN'comp : IsCompIn N' X := hNcomp.map_conj htX
    have hN'N : N' ≠ N := fun heq =>
      htN (CFSG.EvenSporadicStandard.Solomon78.mem_normalizer_iff_map_conj_eq.2 heq)
    have hcardN' : Nat.card N' = Nat.card N :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have htcomm : ∀ k ∈ K, t * k * t⁻¹ = k := fun k hk => by
      have := mem_centralizer_iff.1 htK k hk
      calc t * k * t⁻¹ = (k * t) * t⁻¹ := by rw [this]
        _ = k := by group
    have hN'K : N' ≠ K := by
      intro heq
      apply hNK
      have hle : N ≤ K := by
        intro n hn
        have h1 : t * n * t⁻¹ ∈ K := by
          rw [← heq]
          exact ⟨n, hn, rfl⟩
        have h6 : n = t * n * t⁻¹ := by
          have := htcomm _ h1
          calc n = (t * t) * n * (t * t)⁻¹ := by rw [ht2]; group
            _ = t * (t * n * t⁻¹) * t⁻¹ := by group
            _ = t * n * t⁻¹ := this
        rw [h6]
        exact h1
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hNN' : ∀ a ∈ N, ∀ b ∈ N', a * b = b * a := fun a ha b hb =>
      hNcomp.commute_of_ne hN'comp hN'N.symm a ha b hb
    have hN'cent : ∀ a ∈ N', ∀ b ∈ K, b * a = a * b := fun a ha b hb =>
      (hN'comp.commute_of_ne hK hN'K a ha b hb).symm
    have hmemN' : ∀ n : ↥N, t * (n : G) * t⁻¹ ∈ N' := fun n => ⟨n, n.2, rfl⟩
    let φ : ↥N →* G :=
      { toFun := fun n => (n : G) * (t * (n : G) * t⁻¹)
        map_one' := by simp
        map_mul' := by
          intro n m
          have hc := hNN' (m : G) m.2 _ (hmemN' n)
          show ((n * m : ↥N) : G) * (t * ((n * m : ↥N) : G) * t⁻¹) =
            ((n : G) * (t * (n : G) * t⁻¹)) * ((m : G) * (t * (m : G) * t⁻¹))
          calc ((n * m : ↥N) : G) * (t * ((n * m : ↥N) : G) * t⁻¹)
              = (n : G) * (m * (t * (n : G) * t⁻¹)) * (t * (m : G) * t⁻¹) := by
                simp only [Subgroup.coe_mul]; group
            _ = (n : G) * ((t * (n : G) * t⁻¹) * m) * (t * (m : G) * t⁻¹) := by rw [hc]
            _ = _ := by group }
    have hφ : ∀ n : ↥N, φ n = (n : G) * (t * (n : G) * t⁻¹) := fun n => rfl
    have hDΛ : φ.range ≤ normalizer (L : Set G) ⊓ centralizer (K : Set G) := by
      rintro _ ⟨n, rfl⟩
      rw [hφ]
      have hn' := hmemN' n
      refine ⟨hCt (mem_centralizer_singleton_iff.2 ?_), mem_centralizer_iff.2 ?_⟩
      ·
        have hc := hNN' (n : G) n.2 _ hn'
        have h1 : t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹ =
            (t * (n : G) * t⁻¹) * (n : G) := by
          calc t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹
              = (t * (n : G) * t⁻¹) * ((t * t) * (n : G) * (t * t)⁻¹) := by group
            _ = (t * (n : G) * t⁻¹) * (n : G) := by rw [ht2]; group
        have h2 : ((n : G) * (t * (n : G) * t⁻¹)) * t =
            t * ((n : G) * (t * (n : G) * t⁻¹)) := by
          have h3 : t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹ =
              (n : G) * (t * (n : G) * t⁻¹) := by rw [h1, ← hc]
          calc ((n : G) * (t * (n : G) * t⁻¹)) * t
              = (t * ((n : G) * (t * (n : G) * t⁻¹)) * t⁻¹) * t := by rw [h3]
            _ = t * ((n : G) * (t * (n : G) * t⁻¹)) := by group
        exact h2
      · intro k hk
        calc k * ((n : G) * (t * (n : G) * t⁻¹))
            = (k * (n : G)) * (t * (n : G) * t⁻¹) := by group
          _ = ((n : G) * k) * (t * (n : G) * t⁻¹) := by rw [hNcentK n n.2 k hk]
          _ = (n : G) * (k * (t * (n : G) * t⁻¹)) := by group
          _ = (n : G) * ((t * (n : G) * t⁻¹) * k) := by rw [hN'cent _ hn' k hk]
          _ = ((n : G) * (t * (n : G) * t⁻¹)) * k := by group
    have hDsolv : Group.IsSolvable ↥φ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDΛ)
        (Subgroup.inclusion_injective hDΛ)
    have hNperf : Group.IsPerfect ↥N := by
      have := CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective K (MulAut.conj h).toMonoidHom (MulAut.conj h).injective) hKq
      exact this.1
    have hDperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hDnontriv : Nontrivial ↥φ.range := by
      by_contra hsub
      rw [not_nontrivial_iff_subsingleton] at hsub
      apply hN'N
      have hle : N' ≤ N := by
        rintro _ ⟨n, hn, rfl⟩
        have h1 : φ ⟨n, hn⟩ = 1 := by
          have := hsub.elim ⟨φ ⟨n, hn⟩, ⟨_, rfl⟩⟩ 1
          exact congrArg Subtype.val this
        rw [hφ] at h1
        have h2 : t * n * t⁻¹ = n⁻¹ := by
          have := congrArg (fun z => n⁻¹ * z) h1
          simpa [mul_assoc] using this
        show t * n * t⁻¹ ∈ N
        rw [h2]
        exact N.inv_mem hn
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
    exact Group.IsPerfect.not_isSolvable ↥φ.range hDsolv

end CFSG.EvenSporadicStandard.Induction
