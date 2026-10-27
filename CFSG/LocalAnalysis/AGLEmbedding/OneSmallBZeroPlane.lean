module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_commute_of_plane {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hAcard : Nat.card A = p ^ 2) {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G)) {k : ℕ}
    (hxk : x ^ p ^ k = 1) : ∃ a₀ ∈ A, a₀ ≠ 1 ∧ x * a₀ * x⁻¹ = a₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hxA
  let act : MulAction (Subgroup.zpowers x) A :=
    MulAction.compHom A (Subgroup.inclusion hle)
  have hpg : IsPGroup p (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
    exact ⟨j, hj⟩
  have hmod := hpg.card_modEq_card_fixedPoints A
  rw [hAcard] at hmod
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) A) := by
    have h0 : p ^ 2 % p = 0 := by
      rw [Nat.pow_mod, Nat.mod_self, zero_pow (by norm_num), Nat.zero_mod]
    have h2 := hmod.symm
    unfold Nat.ModEq at h2
    exact Nat.dvd_of_mod_eq_zero (by rw [h2, h0])
  have h1mem : (1 : A) ∈ MulAction.fixedPoints (Subgroup.zpowers x) A := fun g => by
    show (Subgroup.inclusion hle g) • (1 : A) = 1
    exact smul_one _
  have hne : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) A) ≠ 1 := by
    intro h1
    rw [h1] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ : ∃ a : MulAction.fixedPoints (Subgroup.zpowers x) A,
      a ≠ ⟨1, h1mem⟩ := by
    by_contra h
    push Not at h
    apply hne
    exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h a, h b]⟩, ⟨⟨1, h1mem⟩⟩⟩
  have hfix := ha₀ ⟨x, Subgroup.mem_zpowers x⟩
  refine ⟨a₀, a₀.2, fun h => ha₀1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have h2 : ((⟨x, hxA⟩ : Subgroup.normalizer (A : Set G)) • a₀ : A) = a₀ := hfix
  exact congrArg Subtype.val h2

theorem exists_pow_mul_pow_of_plane {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hAcard : Nat.card A = p ^ 2) {a z : G} (haA : a ∈ A) (hzA : z ∈ A) (hap : orderOf a = p)
    (hzp : orderOf z = p) (hcomm : Commute a z) (hza : z ∉ Subgroup.zpowers a) :
    ∀ b ∈ A, ∃ i m : ℕ, i < p ∧ m < p ∧ b = a ^ i * z ^ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers z = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers z : Subgroup G) ∣ p := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Subgroup.zpowers a ⊓ Subgroup.zpowers z ≤
        Subgroup.zpowers z)
      rwa [Nat.card_zpowers, hzp] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hzp])
      exact hza ((heq ▸ (inf_le_left : Subgroup.zpowers a ⊓ Subgroup.zpowers z ≤ _))
        (Subgroup.mem_zpowers z))
  let f : Fin p × Fin p → A := fun im =>
    ⟨a ^ (im.1 : ℕ) * z ^ (im.2 : ℕ), A.mul_mem (A.pow_mem haA _) (A.pow_mem hzA _)⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, m⟩ ⟨i', m'⟩ h
    have h1 : a ^ (i : ℕ) * z ^ (m : ℕ) = a ^ (i' : ℕ) * z ^ (m' : ℕ) := congrArg Subtype.val h
    have h2 : (a ^ (i' : ℕ))⁻¹ * a ^ (i : ℕ) = z ^ (m' : ℕ) * (z ^ (m : ℕ))⁻¹ := by
      have hc : Commute (a ^ (i : ℕ)) (z ^ (m : ℕ)) := hcomm.pow_pow _ _
      calc (a ^ (i' : ℕ))⁻¹ * a ^ (i : ℕ)
          = (a ^ (i' : ℕ))⁻¹ * (a ^ (i : ℕ) * z ^ (m : ℕ)) * (z ^ (m : ℕ))⁻¹ := by group
        _ = (a ^ (i' : ℕ))⁻¹ * (a ^ (i' : ℕ) * z ^ (m' : ℕ)) * (z ^ (m : ℕ))⁻¹ := by rw [h1]
        _ = z ^ (m' : ℕ) * (z ^ (m : ℕ))⁻¹ := by group
    have hy : (a ^ (i' : ℕ))⁻¹ * a ^ (i : ℕ) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers z :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers a _))
        (Subgroup.npow_mem_zpowers a _), h2 ▸ Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers z _)
          (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z _))⟩
    rw [hinf, Subgroup.mem_bot] at hy
    have ha : a ^ (i : ℕ) = a ^ (i' : ℕ) := by
      have := hy
      rw [inv_mul_eq_one] at this
      exact this.symm
    have hz : z ^ (m : ℕ) = z ^ (m' : ℕ) := by
      have h3 := h2
      rw [hy] at h3
      rw [eq_comm, mul_inv_eq_one] at h3
      exact h3.symm
    rw [pow_eq_pow_iff_modEq, hap] at ha
    rw [pow_eq_pow_iff_modEq, hzp] at hz
    have hi : (i : ℕ) = i' := by
      have := ha
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at this
    have hm : (m : ℕ) = m' := by
      have := hz
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt m.2, Nat.mod_eq_of_lt m'.2] at this
    exact Prod.ext (Fin.ext hi) (Fin.ext hm)
  have hcard : Nat.card (Fin p × Fin p) = Nat.card A := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, hAcard, sq]
  obtain ⟨e⟩ := Finite.card_eq.mp hcard
  have hsurj := (Finite.injective_iff_surjective_of_equiv e).mp hinj
  intro b hb
  obtain ⟨⟨i, m⟩, him⟩ := hsurj ⟨b, hb⟩
  exact ⟨i, m, i.2, m.2, (congrArg Subtype.val him).symm⟩

theorem exists_axis_of_plane {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) {x z : G} (hxA : x ∈ Subgroup.normalizer (A : Set G)) {k : ℕ}
    (hxk : x ^ p ^ k = 1) (hzA : z ∈ A) (hxz : x * z * x⁻¹ ∉ Subgroup.zpowers z) :
    ∃ a ∈ A, a ≠ 1 ∧ x * a * x⁻¹ = a ∧ ∀ b ∈ A, b ∉ Subgroup.zpowers a →
      ∃ j : ℕ, b ∈ Subgroup.zpowers (x ^ j * z * (x ^ j)⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hconj : ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun b hb => (Subgroup.mem_normalizer_iff.mp hxA b).mp hb
  have hord : ∀ b ∈ A, b ≠ 1 → orderOf b = p := fun b hb hb1 => by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hA.2 b hb)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hb1
    · exact h1
  let φ : A →* A :=
    { toFun := fun b => ⟨x * b * x⁻¹ * (b : G)⁻¹, A.mul_mem (hconj _ b.2) (A.inv_mem b.2)⟩
      map_one' := by ext; simp
      map_mul' := fun b c => by
        ext
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
        have h1 := hcommA _ (A.inv_mem b.2) _ (A.mul_mem (hconj _ c.2) (A.inv_mem c.2))
        calc x * ((b : G) * c) * x⁻¹ * ((b : G) * c)⁻¹
            = x * b * x⁻¹ * ((x * c * x⁻¹ * (c : G)⁻¹) * (b : G)⁻¹) := by group
          _ = x * b * x⁻¹ * ((b : G)⁻¹ * (x * c * x⁻¹ * (c : G)⁻¹)) := by rw [h1]
          _ = x * b * x⁻¹ * (b : G)⁻¹ * (x * c * x⁻¹ * (c : G)⁻¹) := by group }
  have hφ : ∀ b : A, (φ b : G) = x * b * x⁻¹ * (b : G)⁻¹ := fun b => rfl
  have hker : ∀ b : A, b ∈ φ.ker ↔ x * (b : G) * x⁻¹ = b := by
    intro b
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hφ, Subgroup.coe_one, mul_inv_eq_one]
  obtain ⟨a₀, ha₀A, ha₀1, ha₀x⟩ := exists_ne_one_commute_of_plane hp hAcard hxA hxk
  have hzker : (⟨z, hzA⟩ : A) ∉ φ.ker := by
    rw [hker]
    intro h
    exact hxz (h ▸ Subgroup.mem_zpowers z)
  have hkercard : Nat.card φ.ker = p := by
    have hdvd : Nat.card φ.ker ∣ p ^ 2 := hAcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases j
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hjeq
      have : (⟨a₀, ha₀A⟩ : A) ∈ φ.ker := (hker _).mpr ha₀x
      rw [hjeq, Subgroup.mem_bot] at this
      exact ha₀1 (congrArg Subtype.val this)
    · exact pow_one p ▸ hjeq
    · exfalso
      have htop : φ.ker = ⊤ := Subgroup.card_eq_iff_eq_top _ |>.mp (by rw [hjeq, hAcard])
      exact hzker (htop ▸ Subgroup.mem_top _)
  have hrangecard : Nat.card φ.range = p := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hkercard, hAcard] at h1
    have : p * Nat.card φ.range = p * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  set a : G := x * z * x⁻¹ * z⁻¹ with ha
  have haA : a ∈ A := (φ ⟨z, hzA⟩).2
  have ha1 : a ≠ 1 := by
    intro h
    apply hzker
    rw [MonoidHom.mem_ker]
    exact Subtype.ext h
  have hap : orderOf a = p := hord a haA ha1
  have hrange : ∀ b : A, ((φ b : A) : G) ∈ Subgroup.zpowers a := by
    have hle : Subgroup.zpowers (φ ⟨z, hzA⟩) ≤ φ.range :=
      Subgroup.zpowers_le.mpr ⟨_, rfl⟩
    have hφz1 : φ ⟨z, hzA⟩ ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hφzo : orderOf (φ ⟨z, hzA⟩) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hap
    have heq : Subgroup.zpowers (φ ⟨z, hzA⟩) = φ.range :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hrangecard, Nat.card_zpowers, hφzo])
    intro b
    have hb : φ b ∈ Subgroup.zpowers (φ ⟨z, hzA⟩) := heq ▸ (⟨b, rfl⟩ : φ b ∈ φ.range)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hn]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [Subgroup.coe_zpow]; rfl⟩
  have hxa : x * a * x⁻¹ = a := by
    have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : x * a * x⁻¹ = ((φ ⟨x * z * x⁻¹, hconj z hzA⟩ : A) : G) := by
        rw [hφ, ha]
        group
      rw [← conj_zpow, h1]
      exact Subgroup.zpow_mem _ (hrange _) n
    have := commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hap hxN hxk
    calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [this.eq]
      _ = a := by group
  refine ⟨a, haA, ha1, hxa, ?_⟩
  have hxj : ∀ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = a ^ j * z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hxaj : x * a ^ j * x⁻¹ = a ^ j := by rw [← conj_pow, hxa]
      calc x ^ (j + 1) * z * (x ^ (j + 1))⁻¹ = x * (x ^ j * z * (x ^ j)⁻¹) * x⁻¹ := by group
        _ = x * a ^ j * x⁻¹ * (x * z * x⁻¹) := by rw [ih]; group
        _ = a ^ j * (a * z) := by rw [hxaj, ha]; group
        _ = a ^ (j + 1) * z := by group
  have hza : z ∉ Subgroup.zpowers a := by
    intro hz
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply hxz
    have h1 : x * z * x⁻¹ = z := by
      rw [← hn, ← conj_zpow, hxa]
    rw [h1]
    exact Subgroup.mem_zpowers z
  have hzp : orderOf z = p := hord z hzA (fun h => hxz (by rw [h]; simp))
  have hcaz : Commute a z := hcommA a haA z hzA
  intro b hb hba
  obtain ⟨i, m, hi, hm, hbeq⟩ :=
    exists_pow_mul_pow_of_plane hp hAcard haA hzA hap hzp hcaz hza b hb
  rw [hbeq] at hba ⊢
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hba (by simp only [pow_zero, mul_one]; exact Subgroup.npow_mem_zpowers a i)
  obtain ⟨m', -, hmm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_of_lt_prime hm0 hm hp).symm hp.one_lt
  refine ⟨i * m', ?_⟩
  rw [hxj]
  have hpow : (a ^ (i * m') * z) ^ m = a ^ i * z ^ m := by
    rw [(hcaz.pow_left (i * m')).mul_pow, ← pow_mul]
    congr 1
    rw [pow_eq_pow_iff_modEq, hap]
    calc i * m' * m = i * (m * m') := by ring
      _ ≡ i * 1 [MOD p] := Nat.ModEq.mul_left _
          (by unfold Nat.ModEq; rw [hmm', Nat.mod_eq_of_lt hp.one_lt])
      _ = i := mul_one i
  rw [← hpow]
  exact Subgroup.npow_mem_zpowers _ m

end CFSG.AGLEmbedding
