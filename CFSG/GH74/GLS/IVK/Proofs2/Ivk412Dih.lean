module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.IVK.Proofs2.DihedralCenter
public import CFSG.RankThree.Literature.ThompsonDihedralProduct

public section

open Subgroup

namespace CFSG.GH74.GLS.IVK.Proofs2

section Dih

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_dihedral_of_inverting {ρ σ : G} {n : ℕ} (hn : 3 ≤ n)
    (hρ : orderOf ρ = 2 ^ (n - 1)) (hσ : σ * σ = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) :
    Nonempty (closure ({ρ, σ} : Set G) ≃* DihedralGroup (2 ^ (n - 1))) := by
  have hσ2 : σ ^ 2 = 1 := by rw [pow_two]; exact hσ
  have hnot : σ ∉ zpowers ρ := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hc : σ * ρ * σ⁻¹ = ρ := by
      rw [← hk]
      group
    have h2 : ρ ^ 2 = 1 := by
      have : ρ = ρ⁻¹ := hc.symm.trans hrel
      have h3 : ρ * ρ = 1 := by
        calc ρ * ρ = ρ * ρ⁻¹ := by rw [← this]
          _ = 1 := mul_inv_cancel ρ
      rwa [pow_two]
    have hd : 2 ^ (n - 1) ∣ 2 := hρ ▸ orderOf_dvd_of_pow_eq_one h2
    have h4 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  obtain ⟨e⟩ := CFSG.RankThree.Literature.nonempty_closure_mulEquiv_dihedralGroup hσ2 hrel hnot
  rw [hρ] at e
  exact ⟨e⟩

theorem isDihedralTwoGroup_closure {ρ σ : G} {n : ℕ} (hn : 3 ≤ n)
    (hρ : orderOf ρ = 2 ^ (n - 1)) (hσ : σ * σ = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) :
    IsDihedralTwoGroup ↥(closure ({ρ, σ} : Set G)) n := by
  obtain ⟨e⟩ := exists_mulEquiv_dihedral_of_inverting hn hρ hσ hrel
  refine ⟨by omega, 2 ^ (n - 1), ?_, ?_, ⟨e⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem dihedral_center_pair {ρ σ : G} {n : ℕ} (hn : 3 ≤ n)
    (hρ : orderOf ρ = 2 ^ (n - 1)) (hσ : σ * σ = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) :
    ρ ^ 2 ^ (n - 2) ∈ closure ({ρ, σ} : Set G) ∧ orderOf (ρ ^ 2 ^ (n - 2)) = 2 ∧
      (∀ a ∈ closure ({ρ, σ} : Set G), a * ρ ^ 2 ^ (n - 2) = ρ ^ 2 ^ (n - 2) * a) ∧
      ∀ z ∈ closure ({ρ, σ} : Set G), (∀ a ∈ closure ({ρ, σ} : Set G), a * z = z * a) →
        z = 1 ∨ z = ρ ^ 2 ^ (n - 2) := by
  have hρmem : ρ ∈ closure ({ρ, σ} : Set G) := subset_closure (by simp)
  have hn2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp [pow_succ]
    ring
  have hord : orderOf (ρ ^ 2 ^ (n - 2)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hρ]; exact pow_dvd_pow 2 (by omega)), hρ, hn2]
    have : 0 < 2 ^ (n - 2) := by positivity
    exact Nat.mul_div_cancel _ this
  have hsq : ρ ^ 2 ^ (n - 2) * ρ ^ 2 ^ (n - 2) = 1 := by
    have := pow_orderOf_eq_one (ρ ^ 2 ^ (n - 2))
    rwa [hord, pow_two] at this
  have hcomm : ∀ a ∈ closure ({ρ, σ} : Set G), a * ρ ^ 2 ^ (n - 2) = ρ ^ 2 ^ (n - 2) * a := by
    intro a ha
    have hle : closure ({ρ, σ} : Set G) ≤ centralizer ({ρ ^ 2 ^ (n - 2)} : Set G) := by
      rw [closure_le]
      intro g hg
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hg with rfl | hg
      · exact (Commute.self_pow g _).eq
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        have h1 : g * ρ ^ 2 ^ (n - 2) * g⁻¹ = (ρ ^ 2 ^ (n - 2))⁻¹ := by
          rw [← conj_pow, hrel, inv_pow]
        have h2 : (ρ ^ 2 ^ (n - 2))⁻¹ = ρ ^ 2 ^ (n - 2) := inv_eq_of_mul_eq_one_right hsq
        rw [h2] at h1
        exact mul_inv_eq_iff_eq_mul.1 h1
    exact mem_centralizer_singleton_iff.1 (hle ha)
  refine ⟨pow_mem hρmem _, hord, hcomm, ?_⟩
  intro z hz hzc
  obtain ⟨e⟩ := exists_mulEquiv_dihedral_of_inverting hn hρ hσ hrel
  by_cases hz1 : z = 1
  · exact Or.inl hz1
  · right
    have hcmem : ρ ^ 2 ^ (n - 2) ∈ closure ({ρ, σ} : Set G) := pow_mem hρmem _
    have hc1 : (⟨ρ ^ 2 ^ (n - 2), hcmem⟩ : ↥(closure ({ρ, σ} : Set G))) ≠ 1 := by
      intro h
      have : ρ ^ 2 ^ (n - 2) = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hord
      omega
    have hcc : ∀ h : ↥(closure ({ρ, σ} : Set G)), h * ⟨ρ ^ 2 ^ (n - 2), hcmem⟩ =
        ⟨ρ ^ 2 ^ (n - 2), hcmem⟩ * h := fun h => Subtype.ext (hcomm h.1 h.2)
    have := dihedral_central_unique (k := 2 ^ (n - 1)) (by
        calc 3 ≤ 4 := by norm_num
          _ = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) e
      (z := ⟨z, hz⟩) (z' := ⟨ρ ^ 2 ^ (n - 2), hcmem⟩) (fun h => hz1 (congrArg Subtype.val h))
      (fun h => Subtype.ext (hzc h.1 h.2)) hc1 hcc
    exact congrArg Subtype.val this

theorem card_eq_of_isDihedralTwoGroup {Y : Type} [Group Y] {n : ℕ} (h : IsDihedralTwoGroup Y n) :
    Nat.card Y = 2 ^ n := by
  obtain ⟨-, k, hk, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk]

theorem isDihedralTwoGroup_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {n : ℕ}
    (h : IsDihedralTwoGroup Y n) : IsDihedralTwoGroup Y' n := by
  obtain ⟨hn, k, hk, h2, ⟨e'⟩⟩ := h
  exact ⟨hn, k, hk, h2, ⟨e.symm.trans e'⟩⟩

omit [Finite G] in
theorem commute_of_closure {A B : Set G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ closure A, ∀ y ∈ closure B, x * y = y * x := by
  intro x hx y hy
  have h1 : ∀ b ∈ B, closure A ≤ centralizer ({b} : Set G) := fun b hb => by
    rw [closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact h a ha b hb
  have h2 : closure B ≤ centralizer (closure A : Set G) := by
    rw [closure_le]
    intro b hb
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.1 (h1 b hb ha)
  exact (mem_centralizer_iff.1 (h2 hy) x hx)

@[expose] def Dih412 (G : Type) [Group G] (n : ℕ) (u : G) : Prop :=
  3 ≤ n ∧ orderOf u = 2 ∧
    ∃ D₁ D₂ : Subgroup G, (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧
      IsDihedralTwoGroup ↥D₁ n ∧ IsDihedralTwoGroup ↥D₂ n ∧ u ∈ D₁ ∧ ∀ a ∈ D₁, a * u = u * a

theorem dih412_of_pairs {ρ₁ σ₁ ρ₂ σ₂ : G} {n : ℕ} (hn : 3 ≤ n)
    (h1 : orderOf ρ₁ = 2 ^ (n - 1)) (h2 : orderOf ρ₂ = 2 ^ (n - 1))
    (hσ₁ : σ₁ * σ₁ = 1) (hσ₂ : σ₂ * σ₂ = 1) (hr₁ : σ₁ * ρ₁ * σ₁⁻¹ = ρ₁⁻¹)
    (hr₂ : σ₂ * ρ₂ * σ₂⁻¹ = ρ₂⁻¹) (c11 : ρ₁ * ρ₂ = ρ₂ * ρ₁) (c12 : ρ₁ * σ₂ = σ₂ * ρ₁)
    (c21 : σ₁ * ρ₂ = ρ₂ * σ₁) (c22 : σ₁ * σ₂ = σ₂ * σ₁)
    (hne : ρ₁ ^ 2 ^ (n - 2) ≠ ρ₂ ^ 2 ^ (n - 2)) :
    Dih412 G n (ρ₁ ^ 2 ^ (n - 2)) := by
  obtain ⟨hm1, ho1, hc1, hu1⟩ := dihedral_center_pair hn h1 hσ₁ hr₁
  obtain ⟨hm2, ho2, hc2, hu2⟩ := dihedral_center_pair hn h2 hσ₂ hr₂
  have hcomm : ∀ x ∈ closure ({ρ₁, σ₁} : Set G), ∀ y ∈ closure ({ρ₂, σ₂} : Set G),
      x * y = y * x := by
    apply commute_of_closure
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact c11
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact c12
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact c21
    · rw [Set.mem_singleton_iff] at ha hb
      subst ha hb
      exact c22
  refine ⟨hn, ho1, closure {ρ₁, σ₁}, closure {ρ₂, σ₂}, hcomm, ?_,
    isDihedralTwoGroup_closure hn h1 hσ₁ hr₁, isDihedralTwoGroup_closure hn h2 hσ₂ hr₂, hm1, hc1⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hxc1 : ∀ a ∈ closure ({ρ₁, σ₁} : Set G), a * x = x * a := fun a ha => hcomm a ha x hx2
  have hxc2 : ∀ a ∈ closure ({ρ₂, σ₂} : Set G), a * x = x * a := fun a ha =>
    (hcomm x hx1 a ha).symm
  rcases hu1 x hx1 hxc1 with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rcases hu2 x hx2 hxc2 with h' | h'
    · rw [h']; exact Subgroup.one_mem _
    · exact absurd (h.symm.trans h') hne

end Dih

section Sylow412

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_eq_mul {D₁ D₂ : Subgroup G} (hcomm : ∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a)
    (hinf : D₁ ⊓ D₂ = ⊥) : Nat.card ↥(D₁ ⊔ D₂) = Nat.card ↥D₁ * Nat.card ↥D₂ := by
  have hc : ∀ (m : ↥D₁) (n : ↥D₂), Commute (D₁.subtype m) (D₂.subtype n) := fun m n =>
    hcomm m m.2 n n.2
  set φ : ↥D₁ × ↥D₂ →* G := D₁.subtype.noncommCoprod D₂.subtype hc with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    refine ⟨D₁.subtype_injective, D₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hinf
  have hrange : φ.range = D₁ ⊔ D₂ := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_sylow_two_of_card {k m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ k * m)
    (Q : Sylow 2 G) : Nat.card ↥(Q : Subgroup G) = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Q.card_eq_multiplicity, hcard, Nat.factorization_mul (pow_ne_zero _ (by norm_num))
    hm.pos.ne', Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      obtain ⟨j, hj⟩ := hm
      omega), add_zero]

omit [Finite G] in
theorem mem_sylow_of_commute' (S : Sylow 2 G) {y : G} (hy : ∃ i : ℕ, y ^ 2 ^ i = 1)
    (hc : ∀ x ∈ (S : Subgroup G), Commute x y) : y ∈ (S : Subgroup G) := by
  obtain ⟨i, hi⟩ := hy
  have hz : IsPGroup 2 ↥(zpowers y) := by
    have hdvd : Nat.card ↥(zpowers y) ∣ 2 ^ i := by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hi
    exact IsPGroup.of_card_dvd_pow hdvd
  have hcomm : ∀ x ∈ (S : Subgroup G), ∀ z ∈ zpowers y, Commute x z := by
    intro x hx z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (hc x hx).zpow_right n
  obtain ⟨φ, hrange⟩ : ∃ φ : ↥(S : Subgroup G) × ↥(zpowers y) →* G,
      φ.range = (S : Subgroup G) ⊔ zpowers y :=
    ⟨(S : Subgroup G).subtype.noncommCoprod (zpowers y).subtype
      (fun x z => by
        show Commute (x : G) (z : G)
        exact hcomm x x.2 z z.2), by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]⟩
  have hPQ : IsPGroup 2 (↥(S : Subgroup G) × ↥(zpowers y)) := by
    intro g
    obtain ⟨k₁, hk₁⟩ := S.isPGroup' g.1
    obtain ⟨k₂, hk₂⟩ := hz g.2
    refine ⟨k₁ + k₂, ?_⟩
    have e1 : g.1 ^ 2 ^ (k₁ + k₂) = 1 := by
      rw [pow_add, pow_mul, hk₁, _root_.one_pow]
    have e2 : g.2 ^ 2 ^ (k₁ + k₂) = 1 := by
      rw [pow_add, mul_comm, pow_mul, hk₂, _root_.one_pow]
    exact Prod.ext (by simpa [Prod.pow_fst] using e1) (by simpa [Prod.pow_snd] using e2)
  have hQ : IsPGroup 2 ↥((S : Subgroup G) ⊔ zpowers y) := by
    rw [← hrange]
    exact hPQ.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  have heq := S.is_maximal' hQ le_sup_left
  have : y ∈ (S : Subgroup G) ⊔ zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rw [heq] at this
  exact this

theorem sylow_structure_of_dih412 {n m : ℕ} (hm : Odd m) (hcard : Nat.card G = 2 ^ (2 * n + 1) * m)
    {u : G} (hu : Dih412 G n u) (hnc : ¬ CFSG.GH74.IsCentralInvolution u)
    (S : Sylow 2 ↥(centralizer ({u} : Set G))) :
    ∃ D₁ D₂ : Subgroup G, S.map (centralizer ({u} : Set G)).subtype = D₁ ⊔ D₂ ∧
      (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧ IsDihedralTwoGroup ↥D₁ n ∧
      IsDihedralTwoGroup ↥D₂ n ∧ u ∈ D₁ ∧ (∀ a ∈ D₁, u * a = a * u) ∧
      Nat.card ↥(S.map (centralizer ({u} : Set G)).subtype) = 2 ^ (2 * n) := by
  obtain ⟨hn, hu2, D₁, D₂, hcomm, hinf, hd1, hd2, hu1, hcen⟩ := hu
  revert S
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  intro S
  have hc1 : Nat.card ↥D₁ = 2 ^ n := card_eq_of_isDihedralTwoGroup hd1
  have hc2 : Nat.card ↥D₂ = 2 ^ n := card_eq_of_isDihedralTwoGroup hd2
  have hD1C : D₁ ≤ C := fun a ha => by
    rw [hC, mem_centralizer_singleton_iff]
    exact hcen a ha
  have hD2C : D₂ ≤ C := fun b hb => by
    rw [hC, mem_centralizer_singleton_iff]
    exact (hcomm u hu1 b hb).symm
  set V : Subgroup G := D₁ ⊔ D₂ with hV
  have hVC : V ≤ C := sup_le hD1C hD2C
  have hVcard : Nat.card ↥V = 2 ^ (2 * n) := by
    rw [hV, card_sup_eq_mul hcomm hinf, hc1, hc2, ← pow_add]
    congr 1
    ring
  have hu2' : u ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    have := pow_orderOf_eq_one u
    rwa [hu2] at this
  have key : ∀ P : Subgroup G, P ≤ C → IsPGroup 2 ↥P → Nat.card ↥P ≤ 2 ^ (2 * n) := by
    intro P hPC hP
    by_contra hlt
    replace hlt := not_le.1 hlt
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    have hQcard := card_sylow_two_of_card hm hcard Q
    obtain ⟨j, hj⟩ := hP.exists_card_eq
    have hle : Nat.card ↥P ≤ Nat.card ↥(Q : Subgroup G) := Subgroup.card_le_of_le hPQ
    rw [hj, hQcard] at hle
    rw [hj] at hlt
    have h1 : j ≤ 2 * n + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
    have h2 : 2 * n < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
    have hj' : j = 2 * n + 1 := by omega
    have hPQeq : P = (Q : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hPQ (by rw [hj, hQcard, hj'])
    have hQC : ∀ x ∈ (Q : Subgroup G), Commute x u := by
      intro x hx
      rw [← hPQeq] at hx
      exact mem_centralizer_singleton_iff.1 (hPC hx)
    exact hnc ⟨hu2, Q, mem_sylow_of_commute' Q ⟨1, hu2'⟩ hQC, fun s hs => hQC s hs⟩
  set V' : Subgroup ↥C := V.subgroupOf C with hV'
  have hV'card : Nat.card ↥V' = 2 ^ (2 * n) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, hVcard]
  have hV'p : IsPGroup 2 ↥V' := IsPGroup.of_card hV'card
  have hV'max : ∀ {Q : Subgroup ↥C}, IsPGroup 2 ↥Q → V' ≤ Q → Q = V' := by
    intro Q hQ hVQ
    obtain ⟨j, hj⟩ := hQ.exists_card_eq
    have hmapP : IsPGroup 2 ↥(Q.map C.subtype) := by
      apply IsPGroup.of_card (n := j)
      rw [Subgroup.card_map_of_injective C.subtype_injective, hj]
    have hcardQ := key _ (Subgroup.map_subtype_le Q) hmapP
    rw [Subgroup.card_map_of_injective C.subtype_injective] at hcardQ
    exact (Subgroup.eq_of_le_of_card_ge hVQ (by rw [hV'card]; exact hcardQ)).symm
  let S₀ : Sylow 2 ↥C := ⟨V', hV'p, fun {Q} hQ h => hV'max hQ h⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₀ S
  have hcoe : ((g • S₀ : Sylow 2 ↥C) : Subgroup ↥C) =
      (S₀ : Subgroup ↥C).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have hSmap : (S : Subgroup ↥C) = V'.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, hcoe]
  set f : G →* G := (MulAut.conj (g : G)).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj (g : G)).injective
  have hmapeq : (S : Subgroup ↥C).map C.subtype = V.map f := by
    rw [hSmap, Subgroup.map_map]
    have : C.subtype.comp (MulAut.conj g).toMonoidHom = f.comp C.subtype := by
      ext x
      rfl
    rw [this, ← Subgroup.map_map, hV', Subgroup.map_subgroupOf_eq_of_le hVC]
  have hgu : (g : G) * u = u * g := mem_centralizer_singleton_iff.1 g.2
  have hu' : (g : G) * u * (g : G)⁻¹ = u := by
    rw [hgu]
    group
  refine ⟨D₁.map f, D₂.map f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmapeq, hV, Subgroup.map_sup]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hcomm a ha b hb
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g : G) * a * (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) = g * (a * b) * (g : G)⁻¹ := by group
      _ = g * (b * a) * (g : G)⁻¹ := by rw [this]
      _ = (g : G) * b * (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) := by group
  · rw [← Subgroup.map_inf _ _ _ hfinj, hinf, Subgroup.map_bot]
  · exact isDihedralTwoGroup_of_mulEquiv (Subgroup.equivMapOfInjective D₁ f hfinj) hd1
  · exact isDihedralTwoGroup_of_mulEquiv (Subgroup.equivMapOfInjective D₂ f hfinj) hd2
  · exact ⟨u, hu1, by simpa [hf, MulAut.conj_apply] using hu'⟩
  · rintro _ ⟨a, ha, rfl⟩
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc u * ((g : G) * a * (g : G)⁻¹) = ((g : G) * u * (g : G)⁻¹) * ((g : G) * a * (g : G)⁻¹) := by
          rw [hu']
      _ = (g : G) * (u * a) * (g : G)⁻¹ := by group
      _ = (g : G) * (a * u) * (g : G)⁻¹ := by rw [hcen a ha]
      _ = ((g : G) * a * (g : G)⁻¹) * ((g : G) * u * (g : G)⁻¹) := by group
      _ = ((g : G) * a * (g : G)⁻¹) * u := by rw [hu']
  · rw [hmapeq, Subgroup.card_map_of_injective hfinj, hVcard]

end Sylow412

section Transport

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
theorem isCentralInvolution_conj {z : G} (hz : CFSG.GH74.IsCentralInvolution z) (g : G) :
    CFSG.GH74.IsCentralInvolution (g * z * g⁻¹) := by
  obtain ⟨hz2, S, hzS, hzc⟩ := hz
  have hcoe : ((g • S : Sylow 2 G) : Subgroup G) =
      (S : Subgroup G).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  refine ⟨?_, g • S, ?_, ?_⟩
  · have := MulEquiv.orderOf_eq (MulAut.conj g) z
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hz2
  · rw [hcoe]
    exact ⟨z, hzS, rfl⟩
  · intro s hs
    rw [hcoe] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    show g * s' * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * s' * g⁻¹)
    calc g * s' * g⁻¹ * (g * z * g⁻¹) = g * (s' * z) * g⁻¹ := by group
      _ = g * (z * s') * g⁻¹ := by rw [hzc s' hs']
      _ = g * z * g⁻¹ * (g * s' * g⁻¹) := by group

theorem isCentralInvolution_map (e : G ≃* H) {z : G} (hz : CFSG.GH74.IsCentralInvolution z) :
    CFSG.GH74.IsCentralInvolution (e z) := by
  obtain ⟨hz2, S, hzS, hzc⟩ := hz
  let S' : Sylow 2 H := Sylow.ofCard ((S : Subgroup G).map e.toMonoidHom) (by
    rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
      Nat.card_congr e.toEquiv])
  have hS' : (S' : Subgroup H) = (S : Subgroup G).map e.toMonoidHom := Sylow.coe_ofCard _ _
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hz2, S', ?_, ?_⟩
  · rw [hS']
    exact ⟨z, hzS, rfl⟩
  · intro s hs
    rw [hS'] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    show e s' * e z = e z * e s'
    rw [← map_mul, ← map_mul, hzc s' hs']

omit [Finite G] [Finite H] in
theorem Dih412.map {n : ℕ} {u : G} (e : G ≃* H) (h : Dih412 G n u) : Dih412 H n (e u) := by
  obtain ⟨hn, hu2, D₁, D₂, hcomm, hinf, hd1, hd2, hu1, hcen⟩ := h
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨hn, by rw [MulEquiv.orderOf_eq]; exact hu2, D₁.map e.toMonoidHom, D₂.map e.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [← Subgroup.map_inf _ _ _ hinj, hinf, Subgroup.map_bot]
  · exact isDihedralTwoGroup_of_mulEquiv (Subgroup.equivMapOfInjective D₁ e.toMonoidHom hinj) hd1
  · exact isDihedralTwoGroup_of_mulEquiv (Subgroup.equivMapOfInjective D₂ e.toMonoidHom hinj) hd2
  · exact ⟨u, hu1, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    show e a * e u = e u * e a
    rw [← map_mul, ← map_mul, hcen a ha]

omit [Finite G] in
theorem Dih412.conj {n : ℕ} {u : G} (g : G) (h : Dih412 G n u) : Dih412 G n (g * u * g⁻¹) :=
  Dih412.map (MulAut.conj g) h

end Transport

section Prop412

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]

@[expose] def Prop412 (G : Type) [Group G] : Prop :=
  (∀ u v : G, orderOf u = 2 → orderOf v = 2 → ¬ CFSG.GH74.IsCentralInvolution u →
      ¬ CFSG.GH74.IsCentralInvolution v → IsConj u v) ∧
    ∃ n m : ℕ, Odd m ∧ Nat.card G = 2 ^ (2 * n + 1) * m ∧
      ∃ u₀ : G, ¬ CFSG.GH74.IsCentralInvolution u₀ ∧ Dih412 G n u₀

theorem Prop412.map (e : G ≃* H) (h : Prop412 G) : Prop412 H := by
  obtain ⟨hcl, n, m, hm, hcard, u₀, hnc, hD⟩ := h
  refine ⟨?_, n, m, hm, by rw [← Nat.card_congr e.toEquiv]; exact hcard, e u₀, ?_, hD.map e⟩
  · intro u v hu hv hnu hnv
    have hu' : orderOf (e.symm u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (e.symm v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    have hnu' : ¬ CFSG.GH74.IsCentralInvolution (e.symm u) := fun hc => hnu (by
      simpa using isCentralInvolution_map e hc)
    have hnv' : ¬ CFSG.GH74.IsCentralInvolution (e.symm v) := fun hc => hnv (by
      simpa using isCentralInvolution_map e hc)
    have := hcl _ _ hu' hv' hnu' hnv'
    simpa using MonoidHom.map_isConj e.toMonoidHom this
  · intro hc
    apply hnc
    have := isCentralInvolution_map e.symm hc
    simpa using this

theorem Prop412.sylow_strong (h : Prop412 G) {u : G} (hu : orderOf u = 2)
    (hnc : ¬ CFSG.GH74.IsCentralInvolution u) (S : Sylow 2 ↥(centralizer ({u} : Set G))) :
    ∃ (D₁ D₂ : Subgroup G) (n : ℕ), 3 ≤ n ∧
      S.map (centralizer ({u} : Set G)).subtype = D₁ ⊔ D₂ ∧
      (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧ IsDihedralTwoGroup ↥D₁ n ∧
      IsDihedralTwoGroup ↥D₂ n ∧ u ∈ D₁ ∧ (∀ a ∈ D₁, u * a = a * u) ∧
      Nat.card ↥(S.map (centralizer ({u} : Set G)).subtype) = 2 ^ (2 * n) ∧
      ∀ T : Sylow 2 G, Nat.card ↥(T : Subgroup G) = 2 ^ (2 * n + 1) := by
  obtain ⟨hcl, n, m, hm, hcard, u₀, hnc₀, hD⟩ := h
  obtain ⟨g, hg⟩ := isConj_iff.1 (hcl u₀ u hD.2.1 hu hnc₀ hnc)
  have hD' : Dih412 G n u := by
    rw [← hg]
    exact hD.conj g
  obtain ⟨D₁, D₂, hS, hcomm, hinf, hd1, hd2, hu1, hcen, hcard'⟩ :=
    sylow_structure_of_dih412 hm hcard hD' hnc S
  exact ⟨D₁, D₂, n, hD'.1, hS, hcomm, hinf, hd1, hd2, hu1, hcen, hcard',
    fun T => card_sylow_two_of_card hm hcard T⟩

theorem Prop412.sylow (h : Prop412 G) {u : G} (hu : orderOf u = 2)
    (hnc : ¬ CFSG.GH74.IsCentralInvolution u) (S : Sylow 2 ↥(centralizer ({u} : Set G))) :
    ∃ (D₁ D₂ : Subgroup G) (n : ℕ), 3 ≤ n ∧
      S.map (centralizer ({u} : Set G)).subtype = D₁ ⊔ D₂ ∧
      (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧ IsDihedralTwoGroup ↥D₁ n ∧
      IsDihedralTwoGroup ↥D₂ n ∧
      ((∀ a ∈ D₁, u * a = a * u) ∧ u ∈ D₁ ∨ (∀ a ∈ D₂, u * a = a * u) ∧ u ∈ D₂) ∧
      Nat.card ↥(S.map (centralizer ({u} : Set G)).subtype) = 2 ^ (2 * n) ∧
      ∀ T : Sylow 2 G, Nat.card ↥(T : Subgroup G) = 2 ^ (2 * n + 1) := by
  obtain ⟨D₁, D₂, n, hn, hS, hcomm, hinf, hd1, hd2, hu1, hcen, hcard, hT⟩ := h.sylow_strong hu hnc S
  exact ⟨D₁, D₂, n, hn, hS, hcomm, hinf, hd1, hd2, Or.inl ⟨hcen, hu1⟩, hcard, hT⟩

end Prop412

end CFSG.GH74.GLS.IVK.Proofs2
