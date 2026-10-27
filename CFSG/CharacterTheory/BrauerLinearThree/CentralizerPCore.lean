module

public import CFSG.CharacterTheory.BrauerLinearThree.LocalCounting

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

theorem mem_of_normal_sylow {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hP : (P : Subgroup H).Normal) {x : H} {k : ℕ} (hx : x ^ (p ^ k) = 1) :
    x ∈ (P : Subgroup H) := by
  have hzp : IsPGroup p (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hx
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    apply IsPGroup.of_card (n := j)
    rw [Nat.card_zpowers, hj]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have : Q = P := by
    have := Sylow.unique_of_normal P hP
    exact Subsingleton.elim _ _
  rw [← this]
  exact hQ (Subgroup.mem_zpowers x)

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hcard : Nat.card G * Nat.card Z =
    Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
  (hcent : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
    Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
        Nat.card F ^ 3 * (Nat.card F - 1) ∧
      ((∀ g : G, g * Q * g⁻¹ ∉ rootX₁ φ) →
        Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3))

include hZ hZodd h2 hJ hcard hcent in
theorem exists_pcore_of_mem_rootX₁ [Finite G] {Q : G} (hQ : Q ∈ rootX₁ φ) (hQ1 : Q ≠ 1) :
    ∃ N : Subgroup G, N ≤ Subgroup.centralizer {Q} ∧ IsPGroup (ringChar F) N ∧
      ∀ x ∈ Subgroup.centralizer ({Q} : Set G), ∀ k : ℕ, x ^ (ringChar F ^ k) = 1 → x ∈ N := by
  classical
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  set H := Subgroup.centralizer ({Q} : Set G) with hH_def
  set A := centerSub φ with hA_def
  have hQJ : J * Q = Q * J := commute_J_of_mem_rootX₁ hQ
  have hAH : A ≤ H := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_centerSub φ hz hQJ
  have hAcard : Nat.card A * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  have hl : 0 < Nat.card Z := Nat.card_pos
  have hHdvd : Nat.card H ∣ Nat.card F ^ 3 * Nat.card A := by
    have h1 := (hcent Q hQ1 (pow_ringChar_of_mem_rootX₁ hQ)).1
    rw [← hAcard, ← mul_assoc] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hl h1
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hAH
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hddvd : d ∣ ringChar F ^ (f * 3) := by
    rw [hd, mul_comm (Nat.card A) d] at hHdvd
    have := Nat.dvd_of_mul_dvd_mul_right hApos hHdvd
    rwa [hq, ← pow_mul] at this
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hddvd
  set A' : Subgroup H := A.subgroupOf H
  have hA' : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hcop : Nat.Coprime (ringChar F) (Nat.card A') := by
    rw [hA']
    have : Nat.card A ∣ Nat.card F - 1 := ⟨Nat.card Z, hAcard.symm⟩
    exact (coprime_ringChar_card_sub_one F).coprime_dvd_right this
  have hcardH : Nat.card H = Nat.card A' * ringChar F ^ k := by rw [hA', hd, hk]
  have hfus : ∀ a ∈ A', ∀ g : H, g * a * g⁻¹ ∈ A' → g * a * g⁻¹ = a := by
    intro a ha g hg
    rw [Subgroup.mem_subgroupOf] at ha hg
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hg ⊢
    exact conj_eq_of_mem_centerSub φ hZ hZodd h2 hJ hcard ha g hg
  obtain ⟨P⟩ : Nonempty (Sylow (ringChar F) H) := inferInstance
  have hPn := sylow_normal_of_complement_without_fusion A' hcop hcardH hfus P
  refine ⟨(P : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  intro x hx j hxj
  have hx' : (⟨x, hx⟩ : H) ^ (ringChar F ^ j) = 1 := Subtype.ext (by simpa using hxj)
  exact ⟨⟨x, hx⟩, mem_of_normal_sylow P hPn hx', rfl⟩

include hZ hZodd h2 hJ hcard hcent in
theorem exists_pcore_centralizer [Finite G] {Q : G} (hQ1 : Q ≠ 1) (hQp : Q ^ ringChar F = 1) :
    ∃ N : Subgroup G, N ≤ Subgroup.centralizer {Q} ∧ IsPGroup (ringChar F) N ∧
      ∀ x ∈ Subgroup.centralizer ({Q} : Set G), ∀ k : ℕ, x ^ (ringChar F ^ k) = 1 → x ∈ N := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  by_cases hc : ∃ g : G, g * Q * g⁻¹ ∈ rootX₁ φ
  · obtain ⟨g, hg⟩ := hc
    have hg1 : g * Q * g⁻¹ ≠ 1 := by
      intro h
      apply hQ1
      calc Q = g⁻¹ * (g * Q * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    obtain ⟨N, hN, hNp, hNall⟩ :=
      exists_pcore_of_mem_rootX₁ φ hZ hZodd h2 hJ hcard hcent hg hg1
    refine ⟨N.map (conjHom g⁻¹), ?_, hNp.map _, ?_⟩
    · rintro _ ⟨n, hn, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, conjHom_apply, inv_inv]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hN hn)
      calc g⁻¹ * n * g * Q = g⁻¹ * (n * (g * Q * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * Q * g⁻¹) * n) * g := by rw [this]
        _ = Q * (g⁻¹ * n * g) := by group
    · intro x hx k hxk
      have hx' : g * x * g⁻¹ ∈ Subgroup.centralizer ({g * Q * g⁻¹} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
        calc g * x * g⁻¹ * (g * Q * g⁻¹) = g * (x * Q) * g⁻¹ := by group
          _ = g * (Q * x) * g⁻¹ := by rw [hx]
          _ = g * Q * g⁻¹ * (g * x * g⁻¹) := by group
      have hxk' : (g * x * g⁻¹) ^ (ringChar F ^ k) = 1 := by
        rw [conj_pow, hxk, mul_one, mul_inv_cancel]
      refine ⟨g * x * g⁻¹, hNall _ hx' k hxk', ?_⟩
      rw [conjHom_apply]
      group
  · push Not at hc
    have hdvd := (hcent Q hQ1 hQp).2 hc
    rw [hq, ← pow_mul] at hdvd
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    exact ⟨Subgroup.centralizer {Q}, le_rfl, IsPGroup.of_card ha, fun x hx _ _ => hx⟩

end CFSG.BrauerLinearThree
