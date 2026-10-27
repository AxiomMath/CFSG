module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLatWit

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

section Pair

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}
  [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem map_member {j : ℕ} (hne : Nat.card (C.Y j) ≠ Nat.card Γ) (α : MulAut Γ)
    (hα : C.S.map α.toMonoidHom = C.S) :
    ∃ j' < C.J, (C.Y j).map α.toMonoidHom = C.Y j' ∧ Nat.card (C.Y j') = Nat.card (C.Y j) := by
  have hle : C.S ≤ (C.Y j).map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.map_mono (C.S_le_Y j)
  obtain ⟨j', hj', hZ⟩ := C.complete _ hle
  have hcard : Nat.card ((C.Y j).map α.toMonoidHom) = Nat.card (C.Y j) :=
    Subgroup.card_map_of_injective α.injective
  by_cases hjJ : j' < C.J
  · have hY : (C.Y j).map α.toMonoidHom = C.Y j' := by
      rw [hZ]
      simp [memberOrTop, hjJ]
    refine ⟨j', hjJ, hY, ?_⟩
    rw [← hY]
    exact hcard
  · exfalso
    have hY : (C.Y j).map α.toMonoidHom = ⊤ := by
      rw [hZ]
      simp [memberOrTop, hjJ]
    rw [hY, Subgroup.card_top] at hcard
    exact hne hcard.symm

theorem localPair_of_ctx_pair (hS : IsSylowTwoOf C.S ⊤) (j₁ j₂ ja jb : ℕ)
    (huniq₁ : ∀ j < C.J, Nat.card (C.Y j) = Nat.card (C.Y j₁) → j = j₁)
    (hcb : Nat.card (C.Y jb) = Nat.card (C.Y ja))
    (hM : ∀ j < C.J, Nat.card (C.Y j) = Nat.card (C.Y ja) → j = ja ∨ j = jb)
    (hj₂a : C.Y j₂ ≤ C.Y ja) (hj₂b : C.Y j₂ ≤ C.Y jb)
    (huniq₂ : ∀ j < C.J, Nat.card (C.Y j) = Nat.card (C.Y j₂) → C.Y j ≤ C.Y ja →
      C.Y j ≤ C.Y jb → j = j₂)
    (hne₁ : Nat.card (C.Y j₁) ≠ Nat.card Γ) (hnea : Nat.card (C.Y ja) ≠ Nat.card Γ)
    (hne₂ : Nat.card (C.Y j₂) ≠ Nat.card Γ)
    (hjoin : ∀ j < C.J, ¬ (C.Y j₁ ≤ C.Y j ∧ C.Y j₂ ≤ C.Y j))
    (g₁ : GoodLocal (C.Y j₁)) (g₂ : GoodLocal (C.Y j₂)) : LocalPair Γ := by
  obtain ⟨hS2, hSi⟩ := K1.isSylowTwoOf_top_iff.1 hS
  have hneb : Nat.card (C.Y jb) ≠ Nat.card Γ := by rw [hcb]; exact hnea
  have hne : ∀ (j : ℕ), Nat.card (C.Y j) ≠ Nat.card Γ → C.Y j ≠ ⊤ := by
    intro j h hj
    exact h (by rw [hj, Subgroup.card_top])
  have hinv₁ : ∀ α : MulAut Γ, C.S.map α.toMonoidHom = C.S →
      (C.Y j₁).map α.toMonoidHom = C.Y j₁ := by
    intro α hα
    obtain ⟨j', hj', hY, hc⟩ := map_member C hne₁ α hα
    rw [hY, huniq₁ j' hj' hc]
  have hinv₂ : ∀ α : MulAut Γ, C.S.map α.toMonoidHom = C.S →
      (C.Y j₂).map α.toMonoidHom = C.Y j₂ := by
    intro α hα
    have hinj : Function.Injective (Subgroup.map α.toMonoidHom : Subgroup Γ → Subgroup Γ) :=
      Subgroup.map_injective α.injective
    obtain ⟨ja', hja', hYa, hca⟩ := map_member C hnea α hα
    obtain ⟨jb', hjb', hYb, hcb'⟩ := map_member C hneb α hα
    obtain ⟨j', hj', hY, hc⟩ := map_member C hne₂ α hα
    have hma : ja' = ja ∨ ja' = jb := hM ja' hja' hca
    have hmb : jb' = ja ∨ jb' = jb := hM jb' hjb' (hcb'.trans hcb)
    have hleA : C.Y j' ≤ C.Y ja' := by
      rw [← hYa, ← hY]
      exact Subgroup.map_mono hj₂a
    have hleB : C.Y j' ≤ C.Y jb' := by
      rw [← hYb, ← hY]
      exact Subgroup.map_mono hj₂b
    have hboth : C.Y j' ≤ C.Y ja ∧ C.Y j' ≤ C.Y jb := by
      rcases hma with h | h <;> rcases hmb with h' | h' <;> rw [h] at hYa hleA <;>
        rw [h'] at hYb hleB
      · have h2 : C.Y ja = C.Y jb := by
          apply hinj
          rw [hYa, hYb]
        exact ⟨hleA, by rw [← h2]; exact hleB⟩
      · exact ⟨hleA, hleB⟩
      · exact ⟨hleB, hleA⟩
      · have h2 : C.Y ja = C.Y jb := by
          apply hinj
          rw [hYa, hYb]
        exact ⟨by rw [h2]; exact hleA, hleA⟩
    have := huniq₂ j' hj' hc hboth.1 hboth.2
    rw [hY, this]
  refine ⟨C.S, C.Y j₁, C.Y j₂, hS2, hSi, hinv₁, hinv₂, hne j₁ hne₁, hne j₂ hne₂, ?_, g₁, g₂⟩
  have hle : C.S ≤ C.Y j₁ ⊔ C.Y j₂ := (C.S_le_Y j₁).trans le_sup_left
  obtain ⟨j, hj, hZ⟩ := C.complete _ hle
  by_cases hjJ : j < C.J
  · exfalso
    have hY : C.Y j₁ ⊔ C.Y j₂ = C.Y j := by
      rw [hZ]
      simp [memberOrTop, hjJ]
    exact hjoin j hjJ ⟨hY ▸ le_sup_left, hY ▸ le_sup_right⟩
  · rw [hZ]
    simp [memberOrTop, hjJ]

end Pair

section SylowThree

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem card_commutator_conj (Q : Subgroup Y) [Q.Normal] (g b : Y) :
    Nat.card ↥⁅Q, Subgroup.zpowers (g * b * g⁻¹)⁆ = Nat.card ↥⁅Q, Subgroup.zpowers b⁆ := by
  have hQ : Q.map (MulAut.conj g).toMonoidHom = Q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance x hx g
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
      have := Subgroup.Normal.conj_mem inferInstance y hy g⁻¹
      simpa using this
  have hz : Subgroup.zpowers (g * b * g⁻¹) =
      (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have : ⁅Q, Subgroup.zpowers (g * b * g⁻¹)⁆ =
      (⁅Q, Subgroup.zpowers b⁆).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, hQ, hz]
  rw [this]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem exists_conj_pair {m : ℕ} (hY : Nat.card Y = 9 * m) (hm : ¬ 3 ∣ m) (r₁ r₂ : Y)
    (h₁ : r₁ ^ 3 = 1) (h₂ : r₂ ^ 3 = 1) (hc : r₁ * r₂ = r₂ * r₁) (h1a : r₁ ≠ 1) (h2a : r₂ ≠ 1)
    (h2b : r₂ ≠ r₁) (h2c : r₂ ≠ r₁ ^ 2) {b : Y} (hb : orderOf b = 3) :
    ∃ g : Y, ∃ i < 3, ∃ j < 3, (i ≠ 0 ∨ j ≠ 0) ∧ b = g * (r₁ ^ i * r₂ ^ j) * g⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : Commute r₁ r₂ := hc
  have hmul : ∀ i j i' j' : ℕ, (r₁ ^ i * r₂ ^ j) * (r₁ ^ i' * r₂ ^ j') =
      r₁ ^ (i + i') * r₂ ^ (j + j') := by
    intro i j i' j'
    have h := (hcomm.pow_pow i' j).eq
    calc (r₁ ^ i * r₂ ^ j) * (r₁ ^ i' * r₂ ^ j') = r₁ ^ i * (r₂ ^ j * r₁ ^ i') * r₂ ^ j' := by
          simp only [mul_assoc]
      _ = r₁ ^ i * (r₁ ^ i' * r₂ ^ j) * r₂ ^ j' := by rw [← h]
      _ = r₁ ^ (i + i') * r₂ ^ (j + j') := by simp only [pow_add, mul_assoc]
  set R : Subgroup Y := Subgroup.closure {r₁, r₂} with hR
  have hRel : ∀ x ∈ R, ∃ i j : ℕ, x = r₁ ^ i * r₂ ^ j := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with h | h
      · rw [h]
        exact ⟨1, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨i, j, rfl⟩ := ha
      obtain ⟨i', j', rfl⟩ := hb
      exact ⟨i + i', j + j', hmul i j i' j'⟩
    | inv a _ ha =>
      obtain ⟨i, j, rfl⟩ := ha
      refine ⟨2 * i, 2 * j, ?_⟩
      apply inv_eq_of_mul_eq_one_right
      rw [hmul]
      have e1 : r₁ ^ (i + 2 * i) = 1 := by
        rw [show i + 2 * i = 3 * i by ring, pow_mul, h₁, one_pow]
      have e2 : r₂ ^ (j + 2 * j) = 1 := by
        rw [show j + 2 * j = 3 * j by ring, pow_mul, h₂, one_pow]
      rw [e1, e2, mul_one]
  have hcube : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := hRel x hx
    rw [(hcomm.pow_pow i j).mul_pow]
    have e1 : (r₁ ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h₁, one_pow]
    have e2 : (r₂ ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h₂, one_pow]
    rw [e1, e2, one_mul]
  have hR3 : IsPGroup 3 R := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have := hcube g.1 g.2
    simpa using this
  obtain ⟨P, hRP⟩ := hR3.exists_le_sylow
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := Y)
    omega
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity]
    have hfact : (Nat.card Y).factorization 3 = 2 := by
      rw [hY, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
      have : (9 : ℕ) = 3 ^ 2 := by norm_num
      rw [this, Nat.Prime.factorization_pow Nat.prime_three]
      simp
    rw [hfact]
    norm_num
  have hr1 : Nat.card (Subgroup.zpowers r₁) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime h₁ h1a
  have hr1R : Subgroup.zpowers r₁ ≤ R := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hr2R : r₂ ∈ R := Subgroup.subset_closure (by simp)
  have hRdvd : Nat.card R ∣ 9 := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hRP
  have h3R : 3 ∣ Nat.card R := by
    rw [← hr1]
    exact Subgroup.card_dvd_of_le hr1R
  have hR9 : Nat.card R = 9 := by
    have hcases : Nat.card R = 3 ∨ Nat.card R = 9 := by
      have hd : Nat.card R ∣ 3 ^ 2 := by simpa using hRdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
      interval_cases k
      · rw [pow_zero] at hk'
        rw [hk'] at h3R
        omega
      · left
        simpa using hk'
      · right
        simpa using hk'
    rcases hcases with h | h
    · exfalso
      have heq : Subgroup.zpowers r₁ = R :=
        Subgroup.eq_of_le_of_card_ge hr1R (by rw [h, hr1])
      rw [← heq] at hr2R
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hr2R
      have h1z : r₁ ^ (3 : ℤ) = 1 := by exact_mod_cast h₁
      have hk3 : r₁ ^ k = r₁ ^ (k % 3) := zpow_eq_zpow_emod k h1z
      have hk012 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk012 with h0 | h0 | h0
      · rw [hk3, h0] at hk
        exact h2a (by simpa using hk.symm)
      · rw [hk3, h0] at hk
        exact h2b (by simpa using hk.symm)
      · rw [hk3, h0] at hk
        exact h2c (by rw [← hk]; norm_cast)
    · exact h
  have hRP' : R = (P : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hRP (by rw [hPcard, hR9])
  have hbP : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨Pb, hbPb⟩ := hbP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P Pb
  have hbm : b ∈ ((g • P : Sylow 3 Y) : Set Y) := by
    rw [hg]
    exact hbPb (Subgroup.mem_zpowers b)
  rw [Sylow.coe_smul] at hbm
  obtain ⟨x, hxP, hxb⟩ := Set.mem_smul_set.1 hbm
  have hxb' : b = g * x * g⁻¹ := by
    rw [← hxb]
    rfl
  have hxR : x ∈ R := by
    rw [hRP']
    exact hxP
  obtain ⟨i, j, hij⟩ := hRel x hxR
  have hx3 : r₁ ^ i * r₂ ^ j = r₁ ^ (i % 3) * r₂ ^ (j % 3) := by
    rw [pow_eq_pow_mod i h₁, pow_eq_pow_mod j h₂]
  have hb' : b = g * (r₁ ^ (i % 3) * r₂ ^ (j % 3)) * g⁻¹ := by
    rw [hxb', hij, hx3]
  refine ⟨g, i % 3, Nat.mod_lt _ (by norm_num), j % 3, Nat.mod_lt _ (by norm_num), ?_, hb'⟩
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h0i, h0j⟩ := hcon
  have hb1 : b = 1 := by
    rw [hb', h0i, h0j]
    simp
  rw [hb1, orderOf_one] at hb
  omega

theorem hA3_of_sylow_three {m : ℕ} (hY : Nat.card Y = 9 * m) (hm : ¬ 3 ∣ m) (Q : Subgroup Y)
    [Q.Normal] (r₁ r₂ : Y) (h₁ : r₁ ^ 3 = 1) (h₂ : r₂ ^ 3 = 1) (hc : r₁ * r₂ = r₂ * r₁)
    (h1a : r₁ ≠ 1) (h2a : r₂ ≠ 1) (h2b : r₂ ≠ r₁) (h2c : r₂ ≠ r₁ ^ 2)
    (hP : ∀ i < 3, ∀ j < 3, (i ≠ 0 ∨ j ≠ 0) →
      4 < Nat.card ↥⁅Q, Subgroup.zpowers (r₁ ^ i * r₂ ^ j)⁆) :
    ∀ b : Y, orderOf b = 3 → 4 < Nat.card ↥⁅Q, Subgroup.zpowers b⁆ := by
  intro b hb
  obtain ⟨g, i, hi, j, hj, hne, rfl⟩ := exists_conj_pair hY hm r₁ r₂ h₁ h₂ hc h1a h2a h2b h2c hb
  rw [card_commutator_conj]
  exact hP i hi j hj hne

end SylowThree

section Count

theorem goodLocal_of_count {X : Type*} [Group X] (Y : Subgroup X) [Finite ↥Y] {a c : ℕ}
    (hcard : Nat.card ↥Y = 2 ^ a * 3 ^ c) (hq : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) < 60)
    (hA3 : ∀ b : ↥Y, orderOf b = 3 →
      4 < Nat.card ↥⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆) : GoodLocal Y := by
  set Q : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hcent : ∀ y : ↥Y, (∀ q ∈ Q, y * q = q * y) → y ∈ Q := by
    intro y hy
    set C : Subgroup ↥Y := Subgroup.centralizer (Q : Set ↥Y) with hC
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hyC : y ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro q hq
      exact (hy q hq).symm
    have hC2 : IsPGroup 2 C := by
      rw [IsPGroup.iff_orderOf]
      intro g
      have hdvd : orderOf (g : ↥Y) ∣ 2 ^ a * 3 ^ c := by
        rw [← hcard]
        exact orderOf_dvd_natCard _
      have h3 : ¬ 3 ∣ orderOf (g : ↥Y) := by
        intro h3
        have hcord : orderOf ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3)) = 3 := by
          apply orderOf_pow_orderOf_div (orderOf_pos _).ne' h3
        have hcC : (g : ↥Y) ^ (orderOf (g : ↥Y) / 3) ∈ C := C.pow_mem g.2 _
        have hcQ : ∀ q ∈ Q, q * ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3)) =
            ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3)) * q := fun q hq => by
          have := Subgroup.mem_centralizer_iff.1 hcC q hq
          exact this
        have hbot : ⁅Q, Subgroup.zpowers ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3))⁆ ≤ ⊥ := by
          rw [Subgroup.commutator_le]
          intro q hq z hz
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact ((show Commute q ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3)) from hcQ q hq).zpow_right
            k).eq
        have h5 := hA3 _ hcord
        rw [le_bot_iff.1 hbot, Subgroup.card_bot] at h5
        omega
      have hcop : Nat.Coprime (orderOf (g : ↥Y)) (3 ^ c) :=
        Nat.Coprime.pow_right c ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
      have hd2 : orderOf (g : ↥Y) ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
      exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk⟩
    exact le_pCore_of_normal hC2 hyC
  have hN : ∀ n : ℕ, 2 ≤ n → ¬ (2 ^ n * (4 ^ n - 1) ∣ Nat.card (↥Y ⧸ Q)) := by
    intro n hn
    exact not_dvd_chi0_of_lt Nat.card_pos hq n hn
  exact GoodLocal.of_data Q hQ2 hcent hA3 hN

end Count

end CFSG.QuasithinUnique.Vol2Native.L239
