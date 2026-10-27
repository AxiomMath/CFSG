module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Mat
public import CFSG.ClassicalInvolution.Asc77.AscT7L7
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement

namespace T7V

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem two_ne_zero_galoisField (hp : p ≠ 2) : (2 : GaloisField p f) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).mp h2
  have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
  exact hp this

theorem exists_conj_mod_oddCore (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (ha4 : orderOf a = 4) (hb4 : orderOf b = 4) :
    ∃ k ∈ K, k * a * k⁻¹ * b⁻¹ ∈ oddCoreOf K := by
  obtain ⟨φ⟩ := hΩ.nonempty_equiv_sl2 hK
  have hsq : ∀ {x : G}, x ∈ K → orderOf x = 4 → x * x = z := by
    intro x hx hx4
    have h1 : (x * x) * (x * x) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx4] at this
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    have h2 : x * x ≠ 1 := by
      intro h
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx4] at this
      omega
    exact (hz.unique (x * x) (K.mul_mem hx hx) h1).resolve_left h2
  set mk : ↥K →* ↥K ⧸ classicalInvolutionOddCore ↥K := QuotientGroup.mk' _ with hmk
  have hzK : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
  have hz1 : φ (mk ⟨z, hz.mem⟩) = -1 := by
    have h1 : φ (mk ⟨z, hz.mem⟩) * φ (mk ⟨z, hz.mem⟩) = 1 := by
      rw [← map_mul, ← map_mul, hzK, map_one, map_one]
    rcases sl2_sq_eq_one (two_ne_zero_galoisField hp) h1 with h | h
    · exfalso
      have h2 : mk ⟨z, hz.mem⟩ = 1 := φ.injective (by rw [h, map_one])
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 : z ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨hz.mem, h2⟩
      exact hz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h3
        (isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one))
    · exact h
  have hx : ∀ {x : G} (hxK : x ∈ K), orderOf x = 4 →
      φ (mk ⟨x, hxK⟩) * φ (mk ⟨x, hxK⟩) = -1 := by
    intro x hxK hx4
    rw [← map_mul, ← map_mul]
    have : (⟨x, hxK⟩ : ↥K) * ⟨x, hxK⟩ = ⟨z, hz.mem⟩ := Subtype.ext (hsq hxK hx4)
    rw [this, hz1]
  have hmat : ∀ r : SL(2, GaloisField p f), r * r = -1 →
      (r : Matrix (Fin 2) (Fin 2) (GaloisField p f)) * r = -1 := by
    intro r hr
    have := congrArg (fun m : SL(2, GaloisField p f) =>
      (m : Matrix (Fin 2) (Fin 2) (GaloisField p f))) hr
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg] using this
  obtain ⟨h₁, hh₁⟩ := ModelFacts.Orth15.InnerL4.exists_conj_r0 (two_ne_zero_galoisField hp)
    (φ (mk ⟨a, ha⟩)) (hmat _ (hx ha ha4))
  obtain ⟨h₂, hh₂⟩ := ModelFacts.Orth15.InnerL4.exists_conj_r0 (two_ne_zero_galoisField hp)
    (φ (mk ⟨b, hb⟩)) (hmat _ (hx hb hb4))
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective _ (φ.symm (h₂ * h₁⁻¹))
  refine ⟨k, k.2, ?_⟩
  have hconj : mk k * mk ⟨a, ha⟩ * (mk k)⁻¹ = mk ⟨b, hb⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv]
    have : φ (mk k) = h₂ * h₁⁻¹ := by
      rw [hmk, hk]; exact φ.apply_symm_apply _
    rw [this, ← hh₁, ← hh₂]
    group
  have h3 : mk (k * ⟨a, ha⟩ * k⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hconj]
    group
  rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact mem_oddCoreOf_iff.mpr ⟨by
    have := (k * ⟨a, ha⟩ * k⁻¹ * ⟨b, hb⟩⁻¹).2
    exact this, h3⟩


omit [Finite G] in
theorem conjSub_oddCoreOf_eq_of_mem_normalizer {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    conjSub g (oddCoreOf J) = oddCoreOf J := by
  rw [← Thompson.oddCoreOf_conjSub_eq, mem_normalizer_iff_conjSub_eq.mp hg]

theorem exists_conj_pair (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K ≠ K') {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hKK' : K ≤ trivialOnQuot K') (hK'K : K' ≤ trivialOnQuot K)
    {a a' b₁ b₂ : G} (ha : a ∈ K) (ha' : a' ∈ K') (hb₁ : b₁ ∈ K) (hb₂ : b₂ ∈ K')
    (ha4 : orderOf a = 4) (ha'4 : orderOf a' = 4) (hb₁4 : orderOf b₁ = 4) (hb₂4 : orderOf b₂ = 4)
    (haa' : a * a' = a' * a) (hbb : b₁ * b₂ = b₂ * b₁) :
    ∃ c ∈ K ⊔ K', c * (a * a') * c⁻¹ = b₁ * b₂ := by
  obtain ⟨k, hkK, hk⟩ := exists_conj_mod_oddCore hp hΩ hK hz ha hb₁ ha4 hb₁4
  obtain ⟨k', hk'K', hk'⟩ := exists_conj_mod_oddCore hp hΩ hK' hz' ha' hb₂ ha'4 hb₂4
  have hsq : ∀ {x : G}, orderOf x = 4 → x * x = z → True := fun _ _ => trivial
  have sqz : ∀ {J : Subgroup G} {w x : G}, IsUniqueInvolution J w → x ∈ J → orderOf x = 4 →
      x * x = w := by
    intro J w x hw hx hx4
    have h1 : (x * x) * (x * x) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx4] at this
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    have h2 : x * x ≠ 1 := by
      intro h
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx4] at this
      omega
    exact (hw.unique (x * x) (J.mul_mem hx hx) h1).resolve_left h2
  have hK_nK' : ∀ x ∈ K, x ∈ Subgroup.normalizer (K' : Set G) := fun x hx => (hKK' hx).1
  have hK'_nK : ∀ x ∈ K', x ∈ Subgroup.normalizer (K : Set G) := fun x hx => (hK'K hx).1
  have oK_K : ∀ x ∈ K, ∀ y ∈ oddCoreOf K, x * y * x⁻¹ ∈ oddCoreOf K := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx) hy
  have oK_K' : ∀ x ∈ K', ∀ y ∈ oddCoreOf K, x * y * x⁻¹ ∈ oddCoreOf K := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hK'_nK x hx) hy
  have oK'_K : ∀ x ∈ K, ∀ y ∈ oddCoreOf K', x * y * x⁻¹ ∈ oddCoreOf K' := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hK_nK' x hx) hy
  have oK'_K' : ∀ x ∈ K', ∀ y ∈ oddCoreOf K', x * y * x⁻¹ ∈ oddCoreOf K' := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx) hy
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Subgroup G, N₀ = oddCoreOf K ⊔ oddCoreOf K' := ⟨_, rfl⟩
  have hN₀le : N₀ ≤ K ⊔ K' := by
    rw [hN₀]; exact sup_le_sup (oddCoreOf_le_self K) (oddCoreOf_le_self K')
  have hOK : oddCoreOf K ≤ N₀ := by rw [hN₀]; exact le_sup_left
  have hOK' : oddCoreOf K' ≤ N₀ := by rw [hN₀]; exact le_sup_right
  have hnormK : ∀ x ∈ K, x ∈ Subgroup.normalizer (N₀ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_conjSub_eq, hN₀, Thompson.conjSub_sup,
      conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hx),
      conjSub_oddCoreOf_eq_of_mem_normalizer (hK_nK' x hx)]
  have hnormK' : ∀ x ∈ K', x ∈ Subgroup.normalizer (N₀ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_conjSub_eq, hN₀, Thompson.conjSub_sup,
      conjSub_oddCoreOf_eq_of_mem_normalizer (hK'_nK x hx),
      conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hx)]
  have hnorm : K ⊔ K' ≤ Subgroup.normalizer (N₀ : Set G) :=
    sup_le (fun x hx => hnormK x hx) (fun x hx => hnormK' x hx)
  have hodd : Odd (Nat.card ↥N₀) := by
    have hle : oddCoreOf K ≤ Subgroup.normalizer (oddCoreOf K' : Set G) := fun g hg =>
      mem_normalizer_iff_conjSub_eq.mpr
        (conjSub_oddCoreOf_eq_of_mem_normalizer (hK_nK' g (oddCoreOf_le_self K hg)))
    have hcard :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.card_sup_mul_card_inf_of_le_normalizer
        hle
    have h1 : Odd (Nat.card ↥(oddCoreOf K ⊔ oddCoreOf K') *
        Nat.card ↥(oddCoreOf K ⊓ oddCoreOf K')) := by
      rw [hcard]
      exact (oddCoreOf_odd_natCard K).mul (oddCoreOf_odd_natCard K')
    rw [hN₀]
    exact (Nat.odd_mul.mp h1).1
  have hn₁ : ⁅k', a⁆ ∈ oddCoreOf K := (hK'K hk'K').2 a ha
  have hn₂ : ⁅k, b₂⁆ ∈ oddCoreOf K' := (hKK' hkK).2 b₂ hb₂
  have hm₁ : k * a * k⁻¹ * b₁⁻¹ ∈ oddCoreOf K := hk
  have hm₂ : k' * a' * k'⁻¹ * b₂⁻¹ ∈ oddCoreOf K' := hk'
  have ho₁ : (k * ⁅k', a⁆ * k⁻¹) * (k * a * k⁻¹ * b₁⁻¹) ∈ oddCoreOf K :=
    (oddCoreOf K).mul_mem (oK_K k hkK _ hn₁) hm₁
  have ho₂ : (k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆ ∈ oddCoreOf K' :=
    (oddCoreOf K').mul_mem (oK'_K k hkK _ hm₂) hn₂
  have ho₂' : b₁ * ((k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆) * b₁⁻¹ ∈ oddCoreOf K' :=
    oK'_K b₁ hb₁ _ ho₂
  have hn : ((k * ⁅k', a⁆ * k⁻¹) * (k * a * k⁻¹ * b₁⁻¹)) *
      (b₁ * ((k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆) * b₁⁻¹) ∈ N₀ :=
    N₀.mul_mem (hOK ho₁) (hOK' ho₂')
  obtain ⟨nn, hnneq⟩ : ∃ nn : G, nn = ((k * ⁅k', a⁆ * k⁻¹) * (k * a * k⁻¹ * b₁⁻¹)) *
      (b₁ * ((k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆) * b₁⁻¹) := ⟨_, rfl⟩
  rw [← hnneq] at hn
  have hs'eq : (k * k') * (a * a') * (k * k')⁻¹ = nn * (b₁ * b₂) := by
    rw [hnneq]
    simp only [commutatorElement_def]
    group
  have hb₁b₁ : b₁ * b₁ = z := sqz hz hb₁ hb₁4
  have hb₂b₂ : b₂ * b₂ = z := sqz hz' hb₂ hb₂4
  have haa : a * a = z := sqz hz ha ha4
  have ha'a' : a' * a' = z := sqz hz' ha' ha'4
  have hs2 : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    calc (b₁ * b₂) * (b₁ * b₂) = (b₁ * b₁) * (b₂ * b₂) := by
          rw [mul_assoc, ← mul_assoc b₂, ← hbb]; group
      _ = 1 := by rw [hb₁b₁, hb₂b₂, hz.sq]
  have hu2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a', ← haa']; group
      _ = 1 := by rw [haa, ha'a', hz.sq]
  have hs'2 : ((k * k') * (a * a') * (k * k')⁻¹) * ((k * k') * (a * a') * (k * k')⁻¹) = 1 := by
    calc _ = (k * k') * ((a * a') * (a * a')) * (k * k')⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hu1 : a * a' ≠ 1 := by
    intro h1
    have ha'eq : a' = a⁻¹ := by
      have : a⁻¹ = a' := by
        calc a⁻¹ = a⁻¹ * (a * a') := by rw [h1, mul_one]
          _ = a' := by group
      exact this.symm
    have ha'K : a' ∈ K := by rw [ha'eq]; exact K.inv_mem ha
    have hin : a' ∈ K ⊓ K' := ⟨ha'K, ha'⟩
    have hdvd : 4 ∣ Nat.card ↥(K ⊓ K') := ha'4 ▸ Subgroup.orderOf_dvd_natCard (K ⊓ K') hin
    have hpos : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
      (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
    have := (hΩ.omega4 K hK K' hK' hne).1
    omega
  have hs'1 : (k * k') * (a * a') * (k * k')⁻¹ ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg (fun x => (k * k')⁻¹ * x * (k * k')) h1
    simpa [mul_assoc] using this
  have hbK : b₁ * b₂ ∈ K ⊔ K' := (K ⊔ K').mul_mem (Subgroup.mem_sup_left hb₁)
    (Subgroup.mem_sup_right hb₂)
  obtain ⟨n', hn', hconj⟩ := T7L.exists_conj_involution hodd hs2 hs'2 hs'1 (hnorm hbK) (by
    rw [hs'eq]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm ((K ⊔ K').inv_mem hbK)) nn).mp hn
    have h2 : (b₁ * b₂)⁻¹ * (nn * (b₁ * b₂)) = (b₁ * b₂)⁻¹ * nn * ((b₁ * b₂)⁻¹)⁻¹ := by
      rw [inv_inv]; group
    rw [h2]
    exact h1)
  refine ⟨n'⁻¹ * (k * k'), (K ⊔ K').mul_mem ((K ⊔ K').inv_mem (hN₀le hn'))
    ((K ⊔ K').mul_mem (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right hk'K')), ?_⟩
  calc n'⁻¹ * (k * k') * (a * a') * (n'⁻¹ * (k * k'))⁻¹
      = n'⁻¹ * ((k * k') * (a * a') * (k * k')⁻¹) * n' := by group
    _ = n'⁻¹ * (n' * (b₁ * b₂) * n'⁻¹) * n' := by rw [hconj]
    _ = b₁ * b₂ := by group

end T7V

end CFSG.ClassicalInvolution.Asc77
