module

public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.CGT.PushingUpLit

namespace SubTwo

variable {G : Type*} [Group G]

@[expose] def NoTwoQuotient (Y : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ Y → Y ≤ Subgroup.normalizer (N : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N) → N = Y

theorem exists_pow_mul_eq {Y B : Subgroup G}
    (hnorm : B ≤ Subgroup.normalizer (Y : Set G)) {y q : G} (hy : y ∈ Y) (hq : q ∈ B) (n : ℕ) :
    ∃ y' ∈ Y, (y * q) ^ n = y' * q ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨y', hy', h⟩ := ih
    refine ⟨y * (q * y' * q⁻¹), Y.mul_mem hy ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hnorm hq) y').mp hy'
      exact this
    · rw [pow_succ', h]
      group

theorem exists_pow_mem_of_decomp {Y B P : Subgroup G}
    (hnorm : B ≤ Subgroup.normalizer (Y : Set G)) (hP : IsPGroup 2 P)
    (hdec : ∀ b ∈ B, ∃ y ∈ Y, ∃ q ∈ P, q ∈ B ∧ y * q = b) (b : G) (hb : b ∈ B) :
    ∃ k : ℕ, b ^ 2 ^ k ∈ Y := by
  obtain ⟨y, hy, q, hqP, hqB, rfl⟩ := hdec b hb
  obtain ⟨k, hk⟩ := hP ⟨q, hqP⟩
  refine ⟨k, ?_⟩
  obtain ⟨y', hy', h⟩ := exists_pow_mul_eq hnorm hy hqB (2 ^ k)
  rw [h]
  have hq1 : q ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [hq1, mul_one]
  exact hy'

theorem mem_normalizer_of_normal_chain [Finite G] {Y B B' P : Subgroup G} (hY : NoTwoQuotient Y)
    (hYB : Y ≤ B) (hBn : B ≤ Subgroup.normalizer (Y : Set G))
    (hB'n : B' ≤ Subgroup.normalizer (B : Set G)) (hP : IsPGroup 2 P)
    (hdec : ∀ b ∈ B, ∃ y ∈ Y, ∃ q ∈ P, q ∈ B ∧ y * q = b) {q : G} (hq : q ∈ B') :
    q ∈ Subgroup.normalizer (Y : Set G) := by
  let N : Subgroup G := Y ⊓ Y.comap (MulAut.conj q).toMonoidHom
  have hmem : ∀ x, x ∈ Y.comap (MulAut.conj q).toMonoidHom ↔ q * x * q⁻¹ ∈ Y := fun x => by
    simp [MulAut.conj_apply]
  have hqB : ∀ b ∈ B, q * b * q⁻¹ ∈ B := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp (hB'n hq) b).mp hb
  have hNY : N ≤ Y := inf_le_left
  have hnormN : Y ≤ Subgroup.normalizer (N : Set G) := by
    have key : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
      intro y hy x hx
      obtain ⟨hxY, hxq⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hy hxY) (Y.inv_mem hy), (hmem _).mpr ?_⟩
      have h1 : q * y * q⁻¹ ∈ B := hqB y (hYB hy)
      have h2 : q * x * q⁻¹ ∈ Y := (hmem x).mp hxq
      have h3 := (Subgroup.mem_normalizer_iff.mp (hBn h1) (q * x * q⁻¹)).mp h2
      have : q * (y * x * y⁻¹) * q⁻¹ =
          (q * y * q⁻¹) * (q * x * q⁻¹) * (q * y * q⁻¹)⁻¹ := by group
      rw [this]
      exact h3
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => key y hy x hx, fun hx => ?_⟩
    have := key y⁻¹ (Y.inv_mem hy) _ hx
    simpa [mul_assoc] using this
  have hpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_pow_mem_of_decomp hBn hP hdec (q * y * q⁻¹) (hqB y (hYB hy))
    refine ⟨k, Subgroup.mem_inf.mpr ⟨Y.pow_mem hy _, (hmem _).mpr ?_⟩⟩
    rw [← conj_pow]
    exact hk
  have hNeq : N = Y := hY N hNY hnormN hpow
  have hle : ∀ y ∈ Y, q * y * q⁻¹ ∈ Y := by
    intro y hy
    have hyN : y ∈ N := by rw [hNeq]; exact hy
    exact (hmem y).mp (Subgroup.mem_inf.mp hyN).2
  have hmap : Y.map (MulAut.conj q).toMonoidHom = Y := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hle y hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hle y hy, fun hy => ?_⟩
  have hy' : q * y * q⁻¹ ∈ Y.map (MulAut.conj q).toMonoidHom := by rw [hmap]; exact hy
  obtain ⟨z, hz, hzy⟩ := hy'
  have h2 : q * z * q⁻¹ = q * y * q⁻¹ := by simpa [MulAut.conj_apply] using hzy
  have hzy' : z = y := mul_left_cancel (mul_right_cancel h2)
  rw [← hzy']
  exact hz

theorem normal_of_isSubnormal_sup_eq_top {A : Type*} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : NoTwoQuotient Y) (hP : IsPGroup 2 P) (hPn : P.Normal) (hA : Y ⊔ P = ⊤)
    (hsub : Y.IsSubnormal) : Y.Normal := by
  obtain ⟨n, f, hmono, hnorm, h0, hn⟩ := Subgroup.IsSubnormal.isSubnormal_iff.mp hsub
  have hle : ∀ i, Y ≤ f i := fun i => by rw [← h0]; exact hmono (Nat.zero_le i)
  have := hPn
  have key : ∀ i, f i ≤ Subgroup.normalizer (Y : Set A) := by
    intro i
    induction i with
    | zero => rw [h0]; exact Subgroup.le_normalizer
    | succ i ih =>
      have hBB' : f i ≤ f (i + 1) := hmono (Nat.le_succ i)
      have hB'n : f (i + 1) ≤ Subgroup.normalizer (f i : Set A) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hBB').mp (hnorm i)
      intro b hb
      have hbA : b ∈ Y ⊔ P := by rw [hA]; trivial
      obtain ⟨y, hy, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hbA
      have hqB' : q ∈ f (i + 1) := by
        have : y⁻¹ * (y * q) ∈ f (i + 1) := mul_mem (inv_mem (hle _ hy)) hb
        simpa using this
      have hdec : ∀ c ∈ f i, ∃ y ∈ Y, ∃ q ∈ P, q ∈ f i ∧ y * q = c := by
        intro c hc
        have hcA : c ∈ Y ⊔ P := by rw [hA]; trivial
        obtain ⟨y₁, hy₁, q₁, hq₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hcA
        refine ⟨y₁, hy₁, q₁, hq₁, ?_, rfl⟩
        have : y₁⁻¹ * (y₁ * q₁) ∈ f i := mul_mem (inv_mem (hle _ hy₁)) hc
        simpa using this
      have hqY := mem_normalizer_of_normal_chain hY (hle i) ih hB'n hP hdec hqB'
      exact mul_mem (Subgroup.le_normalizer hy) hqY
  have := key n
  rw [hn] at this
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp this)

theorem noTwoQuotient_subgroupOf {Y A : Subgroup G} (hY : NoTwoQuotient Y) (hYA : Y ≤ A) :
    NoTwoQuotient (Y.subgroupOf A) := by
  intro N' hN'Y hnorm hpow
  let N : Subgroup G := N'.map A.subtype
  have hNY : N ≤ Y := by
    rintro _ ⟨n', hn', rfl⟩
    exact hN'Y hn'
  have key : ∀ y ∈ Y, ∀ x ∈ N, y * x * y⁻¹ ∈ N := by
    rintro y hy _ ⟨n', hn', rfl⟩
    have hy' : (⟨y, hYA hy⟩ : A) ∈ Y.subgroupOf A := hy
    have := (Subgroup.mem_normalizer_iff.mp (hnorm hy') n').mp hn'
    exact ⟨_, this, by simp⟩
  have hnormN : Y ≤ Subgroup.normalizer (N : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => key y hy x hx, fun hx => ?_⟩
    have := key y⁻¹ (Y.inv_mem hy) _ hx
    simpa [mul_assoc] using this
  have hpowN : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    intro y hy
    have hy' : (⟨y, hYA hy⟩ : A) ∈ Y.subgroupOf A := hy
    obtain ⟨k, hk⟩ := hpow _ hy'
    exact ⟨k, _, hk, by simp⟩
  have hNeq : N = Y := hY N hNY hnormN hpowN
  refine le_antisymm hN'Y fun y' hy' => ?_
  have hyY : (y' : G) ∈ Y := hy'
  have : (y' : G) ∈ N := by rw [hNeq]; exact hyY
  obtain ⟨n', hn', hnn⟩ := this
  have : n' = y' := Subtype.ext hnn
  rw [← this]
  exact hn'

theorem le_normalizer_of_isSubnormal_sup [Finite G] {Y P : Subgroup G} (hY : NoTwoQuotient Y)
    (hP : IsPGroup 2 P) (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    (hsub : (Y.subgroupOf (Y ⊔ P)).IsSubnormal) : P ≤ Subgroup.normalizer (Y : Set G) := by
  have hAP : Y ⊔ P ≤ Subgroup.normalizer (P : Set G) :=
    sup_le hYP Subgroup.le_normalizer
  have hYA : Y ≤ Y ⊔ P := le_sup_left
  have hPA : P ≤ Y ⊔ P := le_sup_right
  have hPn : (P.subgroupOf (Y ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPA).mpr hAP
  have hP' : IsPGroup 2 (P.subgroupOf (Y ⊔ P)) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPA).symm
  have hsup : Y.subgroupOf (Y ⊔ P) ⊔ P.subgroupOf (Y ⊔ P) = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (Y ⊔ P))
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYA,
      Subgroup.map_subgroupOf_eq_of_le hPA, Subgroup.map_top, Subgroup.range_subtype]
  have hnorm := normal_of_isSubnormal_sup_eq_top (noTwoQuotient_subgroupOf hY hYA) hP' hPn hsup hsub
  intro p hp
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · have hy' : (⟨y, hYA hy⟩ : ↥(Y ⊔ P)) ∈ Y.subgroupOf (Y ⊔ P) := hy
    exact hnorm.conj_mem _ hy' ⟨p, hPA hp⟩
  · have hz : (⟨p * y * p⁻¹, hYA hy⟩ : ↥(Y ⊔ P)) ∈ Y.subgroupOf (Y ⊔ P) := hy
    have h3 := Subgroup.mem_subgroupOf.mp (hnorm.conj_mem _ hz ⟨p, hPA hp⟩⁻¹)
    simpa [mul_assoc] using h3

theorem noTwoQuotient_of_oResidualTwo {Y : Subgroup G}
    (h : CFSG.RankThree.PartOne.oResidualTwo ↥Y = ⊤) : NoTwoQuotient Y := by
  intro N hNY hnorm hpow
  have hn' : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hnorm
  have hp : IsPGroup 2 (↥Y ⧸ N.subgroupOf Y) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hpow y y.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have hle : CFSG.RankThree.PartOne.oResidualTwo ↥Y ≤ N.subgroupOf Y :=
    sInf_le ⟨hn', hp⟩
  rw [h, top_le_iff] at hle
  refine le_antisymm hNY fun y hy => ?_
  have : (⟨y, hy⟩ : ↥Y) ∈ N.subgroupOf Y := by rw [hle]; trivial
  exact this

end SubTwo

end CFSG.CGT.PushingUpLit
