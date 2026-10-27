module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem core_free_of_equiv {S X : Type} [Group S] [Group X] (e : S ≃* X)
    (hX : ∀ g : X, Odd (orderOf g) → ∀ R : Subgroup X, IsPGroup 2 R → R ≠ ⊥ →
      (∀ r ∈ R, g * r = r * g) → g = 1) :
    ∀ g : S, Odd (orderOf g) → ∀ R : Subgroup S, IsPGroup 2 R → R ≠ ⊥ →
      (∀ r ∈ R, g * r = r * g) → g = 1 := by
  intro g hg R hR hRne hcomm
  have hcardR : Nat.card (R.map e.toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective e.injective
  have key := hX (e g) (by rwa [MulEquiv.orderOf_eq]) (R.map e.toMonoidHom)
    (hR.map e.toMonoidHom) ?_ ?_
  · exact e.map_eq_one_iff.1 key
  · intro hbot
    apply hRne
    apply Subgroup.eq_bot_of_card_eq
    rw [← hcardR, hbot, Subgroup.card_bot]
  · rintro _ ⟨r, hr, rfl⟩
    show e g * e r = e r * e g
    rw [← map_mul, ← map_mul, hcomm r hr]

theorem small_aut_eq_one {H : Type} [Group H] [Finite H]
    (hperf : commutator H = ⊤) (hsimple : IsSimpleGroup (H ⧸ Subgroup.center H))
    (hinn : ∀ φ : MulAut (H ⧸ Subgroup.center H), Odd (orderOf φ) →
      ∃ g : H ⧸ Subgroup.center H, φ = MulAut.conj g)
    (hcore : ∀ g : H ⧸ Subgroup.center H, Odd (orderOf g) → ∀ R : Subgroup (H ⧸ Subgroup.center H),
      IsPGroup 2 R → R ≠ ⊥ → (∀ r ∈ R, g * r = r * g) → g = 1)
    (hZcop : Nat.Coprime (Nat.card (Subgroup.center H)) 2)
    (α : MulAut H) (m : ℕ) (hm : Odd m) (hαm : α ^ m = 1)
    (Q : Subgroup H) (hQp : IsPGroup 2 Q) (hQne : Q ≠ ⊥) (hQfix : ∀ x ∈ Q, α x = x) : α = 1 := by
  have hZS : Subgroup.center (H ⧸ Subgroup.center H) = ⊥ := by
    haveI : Nontrivial (H ⧸ Subgroup.center H) := hsimple.toNontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (H ⧸ Subgroup.center H)) with h | h
    · exact h
    · exfalso
      have hmapT : Subgroup.map (QuotientGroup.mk' (Subgroup.center H)) ⊤ = ⊤ :=
        Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective
      have hcomm_top : commutator (H ⧸ Subgroup.center H) = ⊤ := by
        have h1 := Subgroup.map_commutator (⊤ : Subgroup H) (⊤ : Subgroup H)
          (QuotientGroup.mk' (Subgroup.center H))
        rw [hmapT] at h1
        have h3 : Subgroup.map (QuotientGroup.mk' (Subgroup.center H)) (commutator H) =
            commutator (H ⧸ Subgroup.center H) := h1
        have h2 : Subgroup.map (QuotientGroup.mk' (Subgroup.center H)) (commutator H) = ⊤ := by
          rw [hperf, hmapT]
        exact h3.symm.trans h2
      have hbot : commutator (H ⧸ Subgroup.center H) = ⊥ :=
        (commutator_eq_bot_iff_center_eq_top (H ⧸ Subgroup.center H)).2 h
      obtain ⟨x, hx⟩ := exists_ne (1 : H ⧸ Subgroup.center H)
      have hxc : x ∈ commutator (H ⧸ Subgroup.center H) := by
        rw [hcomm_top]
        exact Subgroup.mem_top x
      rw [hbot] at hxc
      exact hx (Subgroup.mem_bot.1 hxc)
  have hZα : Subgroup.map (α : H →* H) (Subgroup.center H) = Subgroup.center H :=
    Subgroup.map_center_eq α
  let φ : MulAut (H ⧸ Subgroup.center H) :=
    QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) α hZα
  have hφπ : ∀ x : H, φ (x : H ⧸ Subgroup.center H) = ((α x : H) : H ⧸ Subgroup.center H) :=
    fun x => QuotientGroup.congr_mk _ _ α hZα x
  have hφpow : ∀ k : ℕ, ∀ x : H, (φ ^ k) (x : H ⧸ Subgroup.center H) =
      ((α ^ k) x : H ⧸ Subgroup.center H) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      simp only [pow_succ, MulAut.mul_apply]
      rw [hφπ, ih]
  have hφm : φ ^ m = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφpow m x, hαm]
    rfl
  have hφodd : Odd (orderOf φ) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hφm)
  obtain ⟨gb, hgb⟩ := hinn φ hφodd
  have hgbm : gb ^ m = 1 := by
    have h1 : MulAut.conj (gb ^ m) = 1 := by rw [map_pow, ← hgb, hφm]
    have hmem : gb ^ m ∈ Subgroup.center (H ⧸ Subgroup.center H) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun ψ : MulAut (H ⧸ Subgroup.center H) => ψ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hZS, Subgroup.mem_bot] at hmem
    exact hmem
  have hgbodd : Odd (orderOf gb) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hgbm)
  have hodd_inter : ∀ a : H, a ∈ Q → a ∈ Subgroup.center H → a = 1 := by
    intro a haQ haZ
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQp
    have h1 : orderOf a ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard Q haQ
    have h2 : orderOf a ∣ Nat.card (Subgroup.center H) := Subgroup.orderOf_dvd_natCard _ haZ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hcop : Nat.Coprime (orderOf a) (Nat.card (Subgroup.center H)) := by
      rw [hi]
      exact Nat.Coprime.pow_left i hZcop.symm
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) h2)
  let ψ : Q →* (H ⧸ Subgroup.center H) := (QuotientGroup.mk' (Subgroup.center H)).comp Q.subtype
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haZ : (a : H) ∈ Subgroup.center H := (QuotientGroup.eq_one_iff (a : H)).1 ha
    exact Subtype.ext (hodd_inter a a.2 haZ)
  let Rbar : Subgroup (H ⧸ Subgroup.center H) := (⊤ : Subgroup Q).map ψ
  have hRbarcard : Nat.card Rbar = Nat.card Q := by
    rw [Subgroup.card_map_of_injective hψinj, Subgroup.card_top]
  have hRbarp : IsPGroup 2 Rbar := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hQp
    exact (IsPGroup.iff_card).2 ⟨n, by rw [hRbarcard, hn]⟩
  have hRbarne : Rbar ≠ ⊥ := by
    intro hbot
    apply hQne
    apply Subgroup.eq_bot_of_card_eq
    rw [← hRbarcard, hbot, Subgroup.card_bot]
  have hRbarcomm : ∀ r ∈ Rbar, gb * r = r * gb := by
    rintro _ ⟨y, -, rfl⟩
    have hy : φ ((y : H) : H ⧸ Subgroup.center H) = ((y : H) : H ⧸ Subgroup.center H) := by
      rw [hφπ, hQfix y y.2]
    rw [hgb, MulAut.conj_apply] at hy
    exact mul_inv_eq_iff_eq_mul.1 hy
  have hgb1 : gb = 1 := hcore gb hgbodd Rbar hRbarp hRbarne hRbarcomm
  have hφ1 : φ = 1 := by rw [hgb, hgb1, map_one]
  have hαπ : ∀ x : H, ((α x : H) : H ⧸ Subgroup.center H) = (x : H ⧸ Subgroup.center H) := by
    intro x
    rw [← hφπ x, hφ1]
    rfl
  have hαZ : ∀ x : H, (α x)⁻¹ * x ∈ Subgroup.center H := fun x => QuotientGroup.eq.1 (hαπ x)
  have hpert : ∀ a : H, ∃ z ∈ Subgroup.center H, α a = a * z := by
    intro a
    refine ⟨a⁻¹ * α a, ?_, by group⟩
    have h := inv_mem (hαZ a)
    rwa [mul_inv_rev, inv_inv] at h
  exact aut_eq_one_of_central_pert hperf α hpert

theorem small_aut_eq_one_of_iso {X H : Type} [Group X] [Finite X] [Group H] [Finite H]
    (e : H ⧸ Subgroup.center H ≃* X)
    (hinnX : ∀ φ : MulAut X, Odd (orderOf φ) → ∃ g : X, φ = MulAut.conj g)
    (hinvX : ∀ t : X, orderOf t = 2 → ∃ j : ℕ, Nat.card (Subgroup.centralizer {t}) = 2 ^ j)
    (hperf : commutator H = ⊤) (hsimple : IsSimpleGroup (H ⧸ Subgroup.center H))
    (hZcop : Nat.Coprime (Nat.card (Subgroup.center H)) 2)
    (α : MulAut H) (m : ℕ) (hm : Odd m) (hαm : α ^ m = 1)
    (Q : Subgroup H) (hQp : IsPGroup 2 Q) (hQne : Q ≠ ⊥) (hQfix : ∀ x ∈ Q, α x = x) : α = 1 :=
  small_aut_eq_one hperf hsimple (oddInner_transport e hinnX)
    (core_free_of_equiv e fun g hg R hR hRne hc => core_of_involution hinvX g hg R hR hRne hc)
    hZcop α m hm hαm Q hQp hQne hQfix

abbrev I1312Alt8Constrained : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Q : Subgroup H) (α : MulAut H) (m : ℕ),
    commutator H = ⊤ → IsSimpleGroup (H ⧸ Subgroup.center H) →
    (∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a) →
    Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 8)) →
    Nat.Coprime (Nat.card (Subgroup.center H)) 2 → IsPGroup 2 Q → ¬ Q ≤ Subgroup.center H →
    Nat.Coprime m 2 → α ^ m = 1 → (∀ x ∈ Q, α x = x) →
    (∀ t ∈ pCoreOf 2 (Subgroup.normalizer (Q : Set H)), α t = t) → α = 1

end CFSG.LocalAnalysis.GLTheoremA
