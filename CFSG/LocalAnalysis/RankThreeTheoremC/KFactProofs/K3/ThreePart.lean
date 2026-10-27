module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Cases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section ThreePart

variable {H : Type} [Group H] [Finite H]

theorem conj_three_distinct {L : Subgroup H} {g : H} (hg : ∃ n : ℕ, g ^ 3 ^ n = 1)
    (hgL : g ∉ normalizer (L : Set H)) :
    L.map (MulAut.conj g).toMonoidHom ≠ L ∧
      L.map (MulAut.conj (g * g)).toMonoidHom ≠ L ∧
      L.map (MulAut.conj (g * g)).toMonoidHom ≠ L.map (MulAut.conj g).toMonoidHom := by
  have h1 : L.map (MulAut.conj g).toMonoidHom ≠ L := fun h => hgL ((cc_map_conj_eq_iff L g).mp h)
  refine ⟨h1, fun h => ?_, fun h => ?_⟩
  · have h2 : g * g ∈ normalizer (L : Set H) := (cc_map_conj_eq_iff L (g * g)).mp h
    obtain ⟨n, hn⟩ := hg
    apply hgL
    have hodd : Odd (3 ^ n) := Odd.pow (by decide)
    obtain ⟨m, hm⟩ := hodd
    have hg2 : g = (g * g) ^ (m + 1) := by
      have h3 : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact hn
      have h4 : (g * g) ^ (m + 1) = g ^ (2 * m + 2) := by
        rw [← sq, ← pow_mul, mul_add, mul_one]
      rw [h4, pow_succ, h3, one_mul]
    rw [hg2]
    exact Subgroup.pow_mem _ h2 _
  · have e1 : (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        L.map (MulAut.conj (g * g)).toMonoidHom := cc_map_conj_map L g g
    rw [← e1] at h
    have h2 := Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective h
    exact h1 h2

@[expose] noncomputable def prodThree (L₁ L₂ L₃ : Subgroup H)
    (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (h23 : ∀ b ∈ L₂, ∀ c ∈ L₃, b * c = c * b) : (↥L₁ × ↥L₂ × ↥L₃) →* H where
  toFun x := (x.1 : H) * (x.2.1 : H) * (x.2.2 : H)
  map_one' := by simp
  map_mul' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
    simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
    have e1 : (b : H) * a' = a' * b := (h12 a' a'.2 b b.2).symm
    have e2 : (c : H) * a' = a' * c := (h13 a' a'.2 c c.2).symm
    have e3 : (c : H) * b' = b' * c := (h23 b' b'.2 c c.2).symm
    calc (a : H) * a' * ((b : H) * b') * ((c : H) * c')
        = a * (a' * b) * b' * (c * c') := by simp only [mul_assoc]
      _ = a * (b * a') * b' * (c * c') := by rw [e1]
      _ = a * b * (a' * b') * (c * c') := by simp only [mul_assoc]
      _ = a * b * (a' * (b' * c)) * c' := by simp only [mul_assoc]
      _ = a * b * (a' * (c * b')) * c' := by rw [e3]
      _ = a * b * ((a' * c) * b') * c' := by simp only [mul_assoc]
      _ = a * b * ((c * a') * b') * c' := by rw [e2]
      _ = a * b * c * (a' * b' * c') := by simp only [mul_assoc]

theorem mem_center_of_eq_inv_mul {L₁ : Subgroup H} (a : ↥L₁) (x y : H)
    (hx : ∀ l ∈ L₁, l * x = x * l) (hy : ∀ l ∈ L₁, l * y = y * l)
    (h : (a : H) = (x * y)⁻¹) : a ∈ Subgroup.center ↥L₁ := by
  rw [Subgroup.mem_center_iff]
  intro l
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [h]
  exact ((Commute.mul_right (hx l l.2) (hy l l.2)).inv_right).eq

theorem not_nine_dvd_card_component_quotient (hH : primeComplementCore (G := H) 3 = ⊥)
    (S : Sylow 3 H) (hSW : Nonempty ((S : Subgroup H) ≃* W3)) {L : Subgroup H}
    (hL : IsComponentOf L ⊤) (hnot : ¬ (S : Subgroup H) ≤ normalizer (L : Set H)) :
    ¬ 9 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  intro h9
  obtain ⟨e⟩ := hSW
  obtain ⟨g, hgS, hgL⟩ := SetLike.not_le_iff_exists.mp hnot
  have hg3 : ∃ n : ℕ, g ^ 3 ^ n = 1 := by
    obtain ⟨n, hn⟩ := S.isPGroup' (⟨g, hgS⟩ : (S : Subgroup H))
    exact ⟨n, congrArg Subtype.val hn⟩
  obtain ⟨hne12, hne13, hne23⟩ := conj_three_distinct hg3 hgL
  set L₂ := L.map (MulAut.conj g).toMonoidHom with hL₂
  set L₃ := L.map (MulAut.conj (g * g)).toMonoidHom with hL₃
  have hc2 : IsComponentOf L₂ ⊤ := isComponentOf_map_conj hL g
  have hc3 : IsComponentOf L₃ ⊤ := isComponentOf_map_conj hL (g * g)
  have h12 : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb =>
    component_commute hL hc2 (Ne.symm hne12) ha hb
  have h13 : ∀ a ∈ L, ∀ c ∈ L₃, a * c = c * a := fun a ha c hc =>
    component_commute hL hc3 (Ne.symm hne13) ha hc
  have h23 : ∀ b ∈ L₂, ∀ c ∈ L₃, b * c = c * b := fun b hb c hc =>
    component_commute hc2 hc3 (Ne.symm hne23) hb hc
  let Ψ := prodThree L L₂ L₃ h12 h13 h23
  have hker : Ψ.ker ≤ (Subgroup.center ↥L).prod
      ((Subgroup.center ↥L₂).prod (Subgroup.center ↥L₃)) := by
    rintro ⟨a, b, c⟩ hx
    have habc : (a : H) * b * c = 1 := hx
    have hab : (a : H) * b = b * a := h12 a a.2 b b.2
    have hac : (a : H) * c = c * a := h13 a a.2 c c.2
    have hbc : (b : H) * c = c * b := h23 b b.2 c c.2
    refine Subgroup.mem_prod.mpr ⟨?_, Subgroup.mem_prod.mpr ⟨?_, ?_⟩⟩
    · exact mem_center_of_eq_inv_mul a b c (fun l hl => h12 l hl b b.2) (fun l hl => h13 l hl c c.2)
        (eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact habc))
    · refine mem_center_of_eq_inv_mul b a c (fun l hl => (h12 a a.2 l hl).symm)
        (fun l hl => (h23 l hl c c.2)) (eq_inv_of_mul_eq_one_left ?_)
      calc (b : H) * (a * c) = a * b * c := by rw [← mul_assoc, ← hab]
        _ = 1 := habc
    · refine mem_center_of_eq_inv_mul c a b (fun l hl => (h13 a a.2 l hl).symm)
        (fun l hl => (h23 b b.2 l hl).symm) (eq_inv_of_mul_eq_one_left ?_)
      calc (c : H) * (a * b) = a * b * c := by
            rw [← mul_assoc, ← hac, mul_assoc, ← hbc, ← mul_assoc]
        _ = 1 := habc
  have hinjc : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hinjc' : Function.Injective (MulAut.conj (g * g)).toMonoidHom := (MulAut.conj (g * g)).injective
  have eq2 : ↥L ≃* ↥L₂ := L.equivMapOfInjective _ hinjc
  have eq3 : ↥L ≃* ↥L₃ := L.equivMapOfInjective _ hinjc'
  have hc2card : Nat.card ↥L₂ = Nat.card ↥L := (Nat.card_congr eq2.toEquiv).symm
  have hc3card : Nat.card ↥L₃ = Nat.card ↥L := (Nat.card_congr eq3.toEquiv).symm
  have hz2 : Nat.card (Subgroup.center ↥L₂) = Nat.card (Subgroup.center ↥L) :=
    (Nat.card_congr (Subgroup.centerCongr eq2).toEquiv).symm
  have hz3 : Nat.card (Subgroup.center ↥L₃) = Nat.card (Subgroup.center ↥L) :=
    (Nat.card_congr (Subgroup.centerCongr eq3).toEquiv).symm
  set z := Nat.card (Subgroup.center ↥L) with hz
  set m := Nat.card (↥L ⧸ Subgroup.center ↥L) with hm
  have hLcard : Nat.card ↥L = m * z := by
    rw [hm, hz]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
  have hkerdvd : Nat.card Ψ.ker ∣ z * (z * z) := by
    have h1 := Subgroup.card_dvd_of_le hker
    have h2 : Nat.card ↥((Subgroup.center ↥L).prod
        ((Subgroup.center ↥L₂).prod (Subgroup.center ↥L₃))) = z * (z * z) := by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
        Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hz2, hz3]
    rwa [h2] at h1
  have hdom : Nat.card (↥L × ↥L₂ × ↥L₃) = (m * z) * ((m * z) * (m * z)) := by
    rw [Nat.card_prod, Nat.card_prod, hc2card, hc3card, hLcard]
  have hkr := Subgroup.card_ker_mul_card_range Ψ
  rw [hdom] at hkr
  have hrdvd : Nat.card Ψ.range ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  have hS81 : Nat.card (S : Subgroup H) = 81 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.RankThree.PartTwo.Sec11.card_wreath
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSmul := Sylow.card_eq_multiplicity S
  have hfac : (Nat.card H).factorization 3 = 4 := by
    have h : (3 : ℕ) ^ (Nat.card H).factorization 3 = 3 ^ 4 := by
      rw [← hSmul, hS81]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  have hnot5 : ¬ 3 ^ 5 ∣ Nat.card H := by
    intro h5
    have := (Nat.prime_three.pow_dvd_iff_le_factorization (Nat.card_pos).ne').mp h5
    omega
  obtain ⟨k', hk'⟩ := hkerdvd
  have hkpos : 0 < Nat.card Ψ.ker := Nat.card_pos
  have hrange : Nat.card Ψ.range = (m * (m * m)) * k' := by
    apply Nat.eq_of_mul_eq_mul_left hkpos
    calc Nat.card Ψ.ker * Nat.card Ψ.range = (m * z) * ((m * z) * (m * z)) := hkr
      _ = (m * (m * m)) * (z * (z * z)) := by ring
      _ = (m * (m * m)) * (Nat.card Ψ.ker * k') := by rw [hk']
      _ = Nat.card Ψ.ker * ((m * (m * m)) * k') := by ring
  have hmdvd : m * (m * m) ∣ Nat.card H := (Dvd.intro k' hrange.symm).trans hrdvd
  obtain ⟨t, ht⟩ := h9
  have h35 : 3 ^ 5 ∣ m * (m * m) := ⟨3 * t ^ 3, by rw [ht]; ring⟩
  exact hnot5 (h35.trans hmdvd)

theorem three_dvd_card_component_quotient (hH : primeComplementCore (G := H) 3 = ⊥)
    {L : Subgroup H} (hL : IsComponentOf L ⊤) : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
  cp_three_dvd_quotient_center ↥L hL.2.2 (three_dvd_card_component hH hL)

end ThreePart

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
