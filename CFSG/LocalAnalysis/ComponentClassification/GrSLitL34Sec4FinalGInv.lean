module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup

variable {G : Type} [Group G]

theorem inf_centralizer_eq_bot_or [Finite G] {B : Subgroup G} (hB8 : Nat.card B = 8) {h : G}
    {e : ℕ} (hpow : h ^ 7 ^ e = 1) (hN : h ∈ normalizer (B : Set G)) :
    B ⊓ centralizer ({h} : Set G) = ⊥ ∨ h ∈ centralizer (B : Set G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := card_modEq_card_inf_centralizer hpow hN
  rw [hB8] at hmod
  have hdvd : Nat.card ↥(B ⊓ centralizer ({h} : Set G)) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 from rfl, ← hB8]
    exact card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk'] at hmod
  interval_cases k
  · exact Or.inl (card_eq_one.mp (by rw [hk', pow_zero]))
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · right
    have hle : B ≤ B ⊓ centralizer ({h} : Set G) :=
      le_of_eq (eq_of_le_of_card_ge inf_le_left (by rw [hk', hB8]; norm_num)).symm
    rw [mem_centralizer_iff]
    intro b hb
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hle hb)).2

theorem zpow_conj_ne [Finite G] {B : Subgroup G} (hB8 : Nat.card B = 8) {h a : G} {e : ℕ}
    (hpow : h ^ 7 ^ e = 1) (hN : h ∈ normalizer (B : Set G)) (hC : h ∉ centralizer (B : Set G))
    (haB : a ∈ B) (ha1 : a ≠ 1) {j : ℤ} (hj : ¬ (7 : ℤ) ∣ j) : h ^ j * a * (h ^ j)⁻¹ ≠ a := by
  intro hfix
  have hgpow : (h ^ j) ^ 7 ^ e = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  have hgen : h ∈ zpowers (h ^ j) := by
    rw [mem_zpowers_zpow_iff]
    obtain ⟨f, -, hf⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp (orderOf_dvd_of_pow_eq_one hpow)
    rw [hf]
    have h7 : ¬ 7 ∣ j.natAbs := fun h7 => hj (Int.natCast_dvd.mpr h7)
    have hcop : Nat.Coprime j.natAbs (7 ^ f) := Nat.Coprime.pow_right f
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7))
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
    exact hcop
  rcases inf_centralizer_eq_bot_or hB8 hgpow (zpow_mem hN j) with hbot | hgC
  · have haC : a ∈ B ⊓ centralizer ({h ^ j} : Set G) := by
      refine mem_inf.mpr ⟨haB, mem_centralizer_singleton_iff.mpr ?_⟩
      calc a * h ^ j = h ^ j * a * (h ^ j)⁻¹ * h ^ j := by rw [hfix]
        _ = h ^ j * a := by group
    rw [hbot, mem_bot] at haC
    exact ha1 haC
  · apply hC
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hgen
    rw [← hm]
    exact zpow_mem hgC m

theorem exists_seven_of_aut [Finite G] {B T : Subgroup G} (hB8 : IsEightGroup B)
    (hTsyl : IsSylowTwoIn T (centralizer (B : Set G)))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G)) :
    ∃ h : G, ∃ e : ℕ, h ∈ normalizer (T : Set G) ∧ h ∈ normalizer (B : Set G) ∧
      h ^ 7 ^ e = 1 ∧ h ∉ centralizer (B : Set G) := by
  obtain ⟨eB⟩ := GrS4.nonempty_mulAut_equiv_GL (E := ↥B)
    (fun u v => Subtype.ext (hB8.1.1 _ u.2 _ v.2)) (fun u => Subtype.ext (hB8.1.2 _ u.2)) hB8.2
  have : Finite (MulAut ↥B) := Finite.of_equiv _ eB.toEquiv.symm
  have hcard : Nat.card (MulAut ↥B) = 168 := by
    rw [Nat.card_congr eB.toEquiv, LocalAnalysis.ComponentInitial.card_GL_three_zmod_two]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := MulAut ↥B) 7 (by rw [hcard]; norm_num)
  obtain ⟨n, hnN, hn⟩ := hAut σ
  obtain ⟨c₀, hc₀C, hnc⟩ := GrS4.exists_mul_mem_normalizer hTsyl hnN
  have hc₀N : c₀ ∈ normalizer (B : Set G) :=
    GrS4.mem_normalizer_of_forall_commute fun y hy => (mem_centralizer_iff.mp hc₀C y hy).symm
  have hxb : ∀ b : ↥B, (n * c₀)⁻¹ * (b : G) * (n * c₀) = (σ b : G) := by
    intro b
    have h1 := hn b
    have h2 := mem_centralizer_iff.mp hc₀C _ (σ b).2
    calc (n * c₀)⁻¹ * (b : G) * (n * c₀) = c₀⁻¹ * (n⁻¹ * b * n) * c₀ := by group
      _ = (σ b : G) := by rw [h1, mul_assoc, h2, ← mul_assoc, inv_mul_cancel, one_mul]
  set x := n * c₀ with hx
  have hxk : ∀ k : ℕ, ∀ b : ↥B, (x ^ k)⁻¹ * (b : G) * x ^ k = ((σ ^ k) b : G) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [pow_succ, pow_succ', MulAut.mul_apply, ← hxb, ← ih]
      group
  obtain ⟨e, q, hq, hoq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 7 (by norm_num)
  refine ⟨x ^ q, e, pow_mem hnc q, pow_mem (mul_mem hnN hc₀N) q, ?_, fun hC => hq ?_⟩
  · rw [← pow_mul, mul_comm, ← hoq, pow_orderOf_eq_one]
  · rw [← hσ]
    refine orderOf_dvd_of_pow_eq_one (MulEquiv.ext fun b => Subtype.ext ?_)
    rw [← hxk q b, MulAut.one_apply]
    have h1 := mem_centralizer_iff.mp hC b b.2
    calc (x ^ q)⁻¹ * (b : G) * x ^ q = (x ^ q)⁻¹ * ((b : G) * x ^ q) := by group
      _ = (b : G) := by rw [h1]; group

theorem mem_normalizer_of_seven [Finite G] {T T₁ B Z : Subgroup G} {a z h : G}
    (hT₁T : T₁ ≤ T) (hT₁64 : Nat.card T₁ ≤ 64) (hsq : ∀ t ∈ T, t ∉ T₁ → t * t ∈ Z)
    (hBT₁ : B ≤ T₁) (hB8 : Nat.card B = 8) (hBsq : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ t ∈ T, b * t = t * b) (hBZ : ∀ b ∈ B, b ∈ Z → b = 1 ∨ b = a)
    (haB : a ∈ B) (hzT₁ : z ∈ T₁) (hza : z * z = a) (ha1 : a ≠ 1)
    (hhT : h ∈ normalizer (T : Set G)) (hhB : h ∈ normalizer (B : Set G))
    (hfix : ∀ j : ℤ, ¬ (7 : ℤ) ∣ j → h ^ j * a * (h ^ j)⁻¹ ≠ a) :
    h ∈ normalizer (T₁ : Set G) := by
  by_contra hN
  have hzkT : ∀ k : ℤ, h ^ k * z * (h ^ k)⁻¹ ∈ T := fun k =>
    (mem_normalizer_iff.mp (zpow_mem hhT k) z).mp (hT₁T hzT₁)
  have hzksq : ∀ k : ℤ, h ^ k * z * (h ^ k)⁻¹ * (h ^ k * z * (h ^ k)⁻¹) =
      h ^ k * a * (h ^ k)⁻¹ := fun k => by rw [← hza]; group
  have hakB : ∀ k : ℤ, h ^ k * a * (h ^ k)⁻¹ ∈ B := fun k =>
    (mem_normalizer_iff.mp (zpow_mem hhB k) a).mp haB
  have hak1 : ∀ k : ℤ, h ^ k * a * (h ^ k)⁻¹ ≠ 1 := fun k h1 => ha1 (by
    calc a = (h ^ k)⁻¹ * (h ^ k * a * (h ^ k)⁻¹) * h ^ k := by group
      _ = 1 := by rw [h1]; group)
  have hmem : ∀ k : ℤ, -1 ≤ k → k ≤ 6 → h ^ k * z * (h ^ k)⁻¹ ∈ T₁ := by
    intro k hk1 hk6
    by_contra hk
    have h1 := hsq _ (hzkT k) hk
    rw [hzksq] at h1
    rcases hBZ _ (hakB k) h1 with h2 | h2
    · exact hak1 k h2
    · by_cases hk0 : k = 0
      · subst hk0
        apply hk
        simpa using hzT₁
      · exact hfix k (by omega) h2
  set Y : Subgroup G := T₁ ⊓ T₁.comap (MulAut.conj h⁻¹).toMonoidHom with hY
  have hmemY : ∀ {y : G}, y ∈ Y ↔ y ∈ T₁ ∧ h⁻¹ * y * h ∈ T₁ := by
    intro y
    rw [hY, mem_inf, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hzY : ∀ k : ℕ, k < 7 → h ^ (k : ℤ) * z * (h ^ (k : ℤ))⁻¹ ∈ Y := by
    intro k hk
    refine hmemY.mpr ⟨hmem k (by omega) (by omega), ?_⟩
    have h1 := hmem ((k : ℤ) - 1) (by omega) (by omega)
    rwa [show h⁻¹ * (h ^ (k : ℤ) * z * (h ^ (k : ℤ))⁻¹) * h =
      h ^ ((k : ℤ) - 1) * z * (h ^ ((k : ℤ) - 1))⁻¹ by group]
  have hBY : B ≤ Y := fun b hb => hmemY.mpr ⟨hBT₁ hb, hBT₁ (by
    have := (mem_normalizer_iff.mp (inv_mem hhB) b).mp hb
    rwa [inv_inv] at this)⟩
  have hYne : Y ≠ T₁ := by
    intro hYT
    apply hN
    have hinvN : h⁻¹ ∈ normalizer (T₁ : Set G) := GrS4.mem_normalizer_of_map_le_self (by
      rintro _ ⟨y, hy, rfl⟩
      have := (hmemY.mp (hYT ▸ hy : y ∈ Y)).2
      simpa using this)
    simpa using inv_mem hinvN
  have hYcard : Nat.card Y * 2 ≤ 64 := by
    have hlt := card_lt_of_lt (lt_of_le_of_ne (inf_le_left : Y ≤ T₁) hYne)
    obtain ⟨m, hm⟩ := card_dvd_of_le (inf_le_left : Y ≤ T₁)
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · interval_cases m
        · rw [hm, mul_zero] at hlt
          exact absurd hlt (Nat.not_lt_zero _)
        · rw [hm, mul_one] at hlt
          exact absurd hlt (lt_irrefl _)
      · exact hm2
    calc Nat.card Y * 2 ≤ Nat.card Y * m := Nat.mul_le_mul_left _ hm2
      _ = Nat.card T₁ := hm.symm
      _ ≤ 64 := hT₁64
  let f : Fin 7 × ↥B → ↥Y := fun p =>
    ⟨h ^ (p.1.val : ℤ) * z * (h ^ (p.1.val : ℤ))⁻¹ * p.2,
      mul_mem (hzY p.1.val p.1.isLt) (hBY p.2.2)⟩
  have hfinj : Function.Injective f := by
    rintro ⟨k, b⟩ ⟨l, b'⟩ hkl
    have h1 : h ^ (k.val : ℤ) * z * (h ^ (k.val : ℤ))⁻¹ * (b : G) =
        h ^ (l.val : ℤ) * z * (h ^ (l.val : ℤ))⁻¹ * (b' : G) := congrArg Subtype.val hkl
    have hsqb : ∀ (m : ℕ) (c : ↥B), (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹ * (c : G)) *
        (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹ * (c : G)) = h ^ (m : ℤ) * a * (h ^ (m : ℤ))⁻¹ := by
      intro m c
      have hc := hBc c c.2 _ (hzkT m)
      calc (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹ * (c : G)) *
            (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹ * (c : G))
          = (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹) * ((c : G) * (h ^ (m : ℤ) * z *
            (h ^ (m : ℤ))⁻¹)) * (c : G) := by group
        _ = (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹) * (h ^ (m : ℤ) * z * (h ^ (m : ℤ))⁻¹) *
            ((c : G) * c) := by rw [hc]; group
        _ = h ^ (m : ℤ) * a * (h ^ (m : ℤ))⁻¹ := by rw [hBsq c c.2, mul_one, hzksq]
    have h2 : h ^ (k.val : ℤ) * a * (h ^ (k.val : ℤ))⁻¹ =
        h ^ (l.val : ℤ) * a * (h ^ (l.val : ℤ))⁻¹ := by
      rw [← hsqb k.val b, ← hsqb l.val b', h1]
    have h3 : h ^ ((k.val : ℤ) - l.val) * a * (h ^ ((k.val : ℤ) - l.val))⁻¹ = a := by
      calc h ^ ((k.val : ℤ) - l.val) * a * (h ^ ((k.val : ℤ) - l.val))⁻¹
          = (h ^ (l.val : ℤ))⁻¹ * (h ^ (k.val : ℤ) * a * (h ^ (k.val : ℤ))⁻¹) *
            h ^ (l.val : ℤ) := by group
        _ = a := by rw [h2]; group
    have hkl' : k = l := by
      by_contra hne
      have hne' : k.val ≠ l.val := fun h => hne (Fin.ext h)
      exact hfix _ (by have := k.isLt; have := l.isLt; omega) h3
    subst hkl'
    refine Prod.ext rfl (Subtype.ext ?_)
    exact mul_left_cancel h1
  have h56 := Nat.card_le_card_of_injective f hfinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, hB8] at h56
  omega

theorem comm_of_seven [Finite G] {T₁ Z : Subgroup G} {a h : G} (hZc : IsCyclic Z)
    (hZ4 : Nat.card Z = 4) (haZ : a ∈ Z) (haa : a * a = 1) (ha1 : a ≠ 1)
    (hcomm : ∀ s ∈ T₁, ∀ t ∈ T₁, s⁻¹ * t⁻¹ * s * t ∈ Z) (hhT₁ : h ∈ normalizer (T₁ : Set G))
    (hha : h * a * h⁻¹ ≠ a) : ∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s := by
  intro s hs t ht
  by_contra hst
  have hu1 : s⁻¹ * t⁻¹ * s * t ≠ 1 := fun h1 => hst (by
    calc s * t = t * s * (s⁻¹ * t⁻¹ * s * t) := by group
      _ = t * s := by rw [h1, mul_one])
  have hs' := (mem_normalizer_iff.mp hhT₁ s).mp hs
  have ht' := (mem_normalizer_iff.mp hhT₁ t).mp ht
  have hconj : h * (s⁻¹ * t⁻¹ * s * t) * h⁻¹ ∈ Z := by
    have := hcomm _ hs' _ ht'
    rwa [show (h * s * h⁻¹)⁻¹ * (h * t * h⁻¹)⁻¹ * (h * s * h⁻¹) * (h * t * h⁻¹) =
      h * (s⁻¹ * t⁻¹ * s * t) * h⁻¹ by group] at this
  obtain ⟨v, hvZ, hvv, hv1, hvh⟩ : ∃ v ∈ Z, v * v = 1 ∧ v ≠ 1 ∧ h * v * h⁻¹ ∈ Z := by
    set u := s⁻¹ * t⁻¹ * s * t with hu
    have huZ : u ∈ Z := hcomm s hs t ht
    by_cases huu : u * u = 1
    · exact ⟨u, huZ, huu, hu1, hconj⟩
    · refine ⟨u * u, mul_mem huZ huZ, ?_, huu, ?_⟩
      · have h4 : (⟨u, huZ⟩ : ↥Z) ^ 4 = 1 := by rw [← hZ4]; exact pow_card_eq_one'
        have := congrArg Subtype.val h4
        rw [SubmonoidClass.coe_pow] at this
        rw [show u * u * (u * u) = u ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
        exact this
      · rw [show h * (u * u) * h⁻¹ = (h * u * h⁻¹) * (h * u * h⁻¹) by group]
        exact mul_mem hconj hconj
  have hva : v = a := GrS4.eq_of_mul_self_eq_one_of_isCyclic hZc hvZ haZ hvv haa hv1 ha1
  subst hva
  apply hha
  refine GrS4.eq_of_mul_self_eq_one_of_isCyclic hZc hvh hvZ ?_ hvv ?_ hv1
  · rw [show h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ by group, hvv]
    group
  · intro h1
    apply hv1
    calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group

theorem inv_of_seven [Finite G] {T₁ Z : Subgroup G} {a c h : G} (hZc : IsCyclic Z)
    (hZ4 : Nat.card Z = 4) (haZ : a ∈ Z) (haa : a * a = 1) (ha1 : a ≠ 1)
    (hab : ∀ s ∈ T₁, ∀ t ∈ T₁, s * t = t * s) (hcc : c * c = 1)
    (hcN : ∀ t ∈ T₁, c * t * c ∈ T₁) (hδ : ∀ t ∈ T₁, c * t * c * t ∈ Z)
    (hhT₁ : h ∈ normalizer (T₁ : Set G)) (hhc : h * c * h⁻¹ * c ∈ T₁) (hha : h * a * h⁻¹ ≠ a) :
    ∀ t ∈ T₁, c * t * c = t⁻¹ := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hequiv : ∀ s ∈ T₁, h * (c * s * c * s) * h⁻¹ =
      c * (h * s * h⁻¹) * c * (h * s * h⁻¹) := by
    intro s hs
    have hy : h * s * h⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hhT₁ s).mp hs
    have hcx : c * (h * c * h⁻¹ * c) * c ∈ T₁ := hcN _ hhc
    have hcy : c * (h * s * h⁻¹) * c ∈ T₁ := hcN _ hy
    have e1 : (h * c * h⁻¹ * c) * (c * (h * s * h⁻¹) * c) * (c * (h * c * h⁻¹ * c) * c) *
        (h * s * h⁻¹) = h * (c * s * c * s) * h⁻¹ := by
      calc _ = h * c * h⁻¹ * (c * c) * h * s * h⁻¹ * (c * c) * h * c * h⁻¹ * (c * c) * h * s *
            h⁻¹ := by group
        _ = h * (c * s * c * s) * h⁻¹ := by rw [hcc]; group
    have e2 : (h * c * h⁻¹ * c) * (c * (h * c * h⁻¹ * c) * c) = 1 := by
      calc _ = h * c * h⁻¹ * (c * c) * h * c * h⁻¹ * (c * c) := by group
        _ = h * c * h⁻¹ * h * c * h⁻¹ := by rw [hcc]; group
        _ = h * (c * c) * h⁻¹ := by group
        _ = 1 := by rw [hcc]; group
    calc h * (c * s * c * s) * h⁻¹
        = (h * c * h⁻¹ * c) * (c * (h * s * h⁻¹) * c) * (c * (h * c * h⁻¹ * c) * c) *
          (h * s * h⁻¹) := e1.symm
      _ = (h * c * h⁻¹ * c) * ((c * (h * c * h⁻¹ * c) * c) * (c * (h * s * h⁻¹) * c)) *
          (h * s * h⁻¹) := by rw [mul_assoc (h * c * h⁻¹ * c), hab _ hcy _ hcx]
      _ = ((h * c * h⁻¹ * c) * (c * (h * c * h⁻¹ * c) * c)) * (c * (h * s * h⁻¹) * c) *
          (h * s * h⁻¹) := by group
      _ = c * (h * s * h⁻¹) * c * (h * s * h⁻¹) := by rw [e2, one_mul]
  intro t ht
  by_contra hne
  have hδ1 : c * t * c * t ≠ 1 := fun h1 => hne (by
    calc c * t * c = c * t * c * t * t⁻¹ := by group
      _ = t⁻¹ := by rw [h1, one_mul])
  obtain ⟨s, hs, hsa⟩ : ∃ s ∈ T₁, c * s * c * s = a := by
    by_cases hdd : c * t * c * t * (c * t * c * t) = 1
    · exact ⟨t, ht, GrS4.eq_of_mul_self_eq_one_of_isCyclic hZc (hδ t ht) haZ hdd haa hδ1 ha1⟩
    · refine ⟨t * t, mul_mem ht ht, ?_⟩
      have htt : c * (t * t) * c * (t * t) = c * t * c * t * (c * t * c * t) := by
        have hct := hcN t ht
        have e3 : c * (t * t) * c * (t * t) = (c * t * c) * (c * t * c) * (t * t) := by
          calc c * (t * t) * c * (t * t) = c * t * (c * c) * t * c * (t * t) := by
                rw [hcc]; group
            _ = (c * t * c) * (c * t * c) * (t * t) := by group
        have e4 : (c * t * c * t) * (c * t * c * t) = (c * t * c) * (c * t * c) * (t * t) := by
          calc (c * t * c * t) * (c * t * c * t) = (c * t * c) * (t * (c * t * c)) * t := by
                group
            _ = (c * t * c) * ((c * t * c) * t) * t := by rw [hab t ht _ hct]
            _ = (c * t * c) * (c * t * c) * (t * t) := by group
        rw [e3, e4]
      rw [htt]
      have h4 : (⟨c * t * c * t, hδ t ht⟩ : ↥Z) ^ 4 = 1 := by rw [← hZ4]; exact pow_card_eq_one'
      have h4' := congrArg Subtype.val h4
      rw [SubmonoidClass.coe_pow] at h4'
      refine GrS4.eq_of_mul_self_eq_one_of_isCyclic hZc
        (mul_mem (hδ t ht) (hδ t ht)) haZ ?_ haa hdd ha1
      rw [show c * t * c * t * (c * t * c * t) * (c * t * c * t * (c * t * c * t)) =
        (c * t * c * t) ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact h4'
  apply hha
  have hsh : h * s * h⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hhT₁ s).mp hs
  have h1 : h * a * h⁻¹ ∈ Z := by
    rw [← hsa, hequiv s hs]
    exact hδ _ hsh
  refine GrS4.eq_of_mul_self_eq_one_of_isCyclic hZc h1 haZ ?_ haa ?_ ha1
  · rw [show h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ by group, haa]
    group
  · intro h2
    apply ha1
    calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group

end CFSG.ComponentClassification.GrSLit.FinalG
