module

public import CFSG.GH74.GLS.IVK.L2.Lemma12k

public section

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

namespace CFSG.GH74.GLS.LU.Local.Five

section CbarE

theorem kleinFix_eight_dvd {q p n : ℕ} (hp : Odd p) (hq : q = p ^ n) (hn : 2 ∣ n) :
    8 ∣ q * (q ^ 2 - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  obtain ⟨m, hm⟩ := hp.pow (n := k)
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self m
  have hq1 : q = 8 * j + 1 := by
    have h1 : q = (p ^ k) ^ 2 := by rw [hq, ← pow_mul, mul_comm]
    have h2 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    rw [h1, hm, h2, hj]
    ring
  have hsq : q ^ 2 - 1 = 16 * (j * (4 * j + 1)) := by
    have h3 : q ^ 2 = 16 * (j * (4 * j + 1)) + 1 := by rw [hq1]; ring
    omega
  rw [hsq]
  have h4 : q * (16 * (j * (4 * j + 1))) = 2 * (8 * (q * (j * (4 * j + 1)))) := by ring
  rw [h4, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact Dvd.intro _ rfl

theorem kleinFix_not_elemAbelian_eight {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]
    (e : K ≃* L2 F) (hF : L2Field F) (hK2 : (Nat.card K).factorization 2 = 2)
    (E : Subgroup (MulAut K)) (hE8 : Nat.card E = 8)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := fun g => ⟨1, by
    apply Subtype.ext
    show (g : MulAut K) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    exact hsq g g.2⟩
  obtain ⟨T, hT⟩ := hE2.exists_le_sylow
  have hnot : ¬ E ≤ innDiagSub e := by
    intro hsub
    have := card_le_four_of_le_inf e hF T E hT hsub hcomm hsq
    omega
  obtain ⟨y, hyE, hyG⟩ := Set.not_subset.mp hnot
  have hy2 : fieldProj e y ^ 2 = 1 := by
    rw [← map_pow, pow_two, hsq y hyE, map_one]
  have hy1 : fieldProj e y ≠ 1 := fun h => hyG ((mem_innDiagSub_iff e y).mpr h)
  have hord : orderOf (fieldProj e y) = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨p, n, hp, hpodd, -, hpn⟩ := isOddPrimePower_of_L2Field hF
  have hdiv : 2 ∣ n := by
    have h1 : orderOf (fieldProj e y) ∣ Nat.card (F ≃+* F) := orderOf_dvd_natCard _
    rwa [hord, card_ringAut F p n hp hpn] at h1
  have h8 := kleinFix_eight_dvd hpodd hpn hdiv
  rw [← card_eq_of_L2Field e hF] at h8
  have hne : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h23 : 2 ^ 3 ∣ Nat.card K := by simpa using h8
  have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h23
  omega

theorem kleinFix_exists_elemAbelian_eight {M : Type} [Group M] (B : Subgroup M) (hB4 : Nat.card B = 4)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (hBsq : ∀ b ∈ B, b * b = 1) {a : M} (ha : a * a = 1)
    (haB : a ∉ B) (hcomm : ∀ b ∈ B, b * a = a * b) :
    ∃ E : Subgroup M, Nat.card E = 8 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1 := by
  have ha1 : a ≠ 1 := fun h => haB (h ▸ B.one_mem)
  have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hZ : ∀ x ∈ Subgroup.zpowers a, x = 1 ∨ x = a := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk := zpow_mod_orderOf a k
    rw [hord] at hk
    have h2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h | h
    · left
      rw [← hk, h]
      simp
    · right
      rw [← hk, h]
      simp
  have hcommZ : ∀ b ∈ B, ∀ z ∈ Subgroup.zpowers a, b * z = z * b := by
    intro b hb z hz
    rcases hZ z hz with rfl | rfl
    · simp
    · exact hcomm b hb
  have hZc : ∀ z ∈ Subgroup.zpowers a, ∀ z' ∈ Subgroup.zpowers a, z * z' = z' * z := by
    intro z hz z' hz'
    rcases hZ z hz with rfl | rfl
    · simp
    · rcases hZ z' hz' with rfl | rfl
      · simp
      · rfl
  have hZsq : ∀ z ∈ Subgroup.zpowers a, z * z = 1 := by
    intro z hz
    rcases hZ z hz with rfl | rfl
    · simp
    · exact ha
  have hcomm' : ∀ (b : B) (z : Subgroup.zpowers a),
      Commute (B.subtype b) ((Subgroup.zpowers a).subtype z) := fun b z => hcommZ b b.2 z z.2
  let f : B × Subgroup.zpowers a →* M :=
    B.subtype.noncommCoprod (Subgroup.zpowers a).subtype hcomm'
  have hf : ∀ b : B, ∀ z : Subgroup.zpowers a, f (b, z) = (b : M) * (z : M) := fun b z => rfl
  have hinj : Function.Injective f := by
    refine (MonoidHom.noncommCoprod_injective B.subtype (Subgroup.zpowers a).subtype hcomm').mpr
      ⟨B.subtype_injective, (Subgroup.zpowers a).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hxB hxZ
    rcases hZ x hxZ with h | h
    · exact h
    · exact absurd (h ▸ hxB) haB
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hB4,
      Nat.card_zpowers, hord]
  · rintro _ ⟨⟨b, z⟩, rfl⟩ _ ⟨⟨b', z'⟩, rfl⟩
    rw [hf, hf]
    have h1 : Commute (b : M) (b' : M) := hBc b b.2 b' b'.2
    have h2 : Commute (b : M) (z' : M) := hcommZ b b.2 z' z'.2
    have h3 : Commute (z : M) (b' : M) := (hcommZ b' b'.2 z z.2).symm
    have h4 : Commute (z : M) (z' : M) := hZc z z.2 z' z'.2
    exact (Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4) :
      Commute ((b : M) * z) ((b' : M) * z'))
  · rintro _ ⟨⟨b, z⟩, rfl⟩
    rw [hf]
    have h1 : Commute (b : M) (z : M) := hcommZ b b.2 z z.2
    have h2 : ((b : M) * z) ^ 2 = (b : M) ^ 2 * (z : M) ^ 2 := h1.mul_pow 2
    rw [← pow_two, h2, pow_two, pow_two, hBsq b b.2, hZsq z z.2, one_mul]

theorem kleinFix_isSimpleGroup {K : Type} [Group K] {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (e : K ≃* L2 F) : IsSimpleGroup K := by
  have h3 : 3 < Nat.card F := hF.2
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  exact (toPSL e).isSimpleGroup

theorem kleinFix_center_eq_bot {K : Type} [Group K] {F : Type} [Field F] [Finite F] (e : K ≃* L2 F) :
    Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hmem : toPSL e z ∈ Subgroup.center (PSL2 F) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h := congrArg (toPSL e) (hz ((toPSL e).symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  rw [psl2_center_eq_bot F, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
  exact hmem

theorem kleinFix_sq_eq_one {H₁ : Type} [Group H₁] [Finite H₁] {L S : Subgroup H₁}
    {F : Type} [Field F] [Finite F] (hF : L2Field F) (eL : ↥L ≃* L2 F)
    (hL2 : (Nat.card ↥L).factorization 2 = 2) (hS4 : Nat.card ↥S = 4) (hSL : S ≤ L) :
    ∀ s ∈ S, s * s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih : HasDihedralSylowTwo ↥L :=
    hasDihedralSylowTwo_of_equiv (toPSL eL).symm
      (psl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower_of_L2Field hF))
  have hcard0 : Nat.card ↥(S.subgroupOf L) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv).trans hS4
  let P : Sylow 2 ↥L := Sylow.ofCard (S.subgroupOf L) (by rw [hL2, hcard0]; norm_num)
  have hP : (P : Subgroup ↥L) = S.subgroupOf L := rfl
  obtain ⟨m, -, ⟨φ⟩⟩ := hdih P
  have hcard : Nat.card ↥(P : Subgroup ↥L) = 2 * 2 ^ m := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hm : m = 1 := by
    have h1 : Nat.card ↥(P : Subgroup ↥L) = 4 := by
      rw [hP]
      exact hcard0
    have h2 : 2 ^ m = 2 ^ 1 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hm
  intro s hs
  have hsL : s ∈ L := hSL hs
  have hsP : (⟨s, hsL⟩ : ↥L) ∈ (P : Subgroup ↥L) := by
    rw [hP, Subgroup.mem_subgroupOf]
    exact hs
  have hx1 : φ ⟨⟨s, hsL⟩, hsP⟩ * φ ⟨⟨s, hsL⟩, hsP⟩ = 1 := by
    generalize φ ⟨⟨s, hsL⟩, hsP⟩ = g
    revert g
    decide
  have hx : (⟨⟨s, hsL⟩, hsP⟩ : ↥(P : Subgroup ↥L)) * ⟨⟨s, hsL⟩, hsP⟩ = 1 := by
    rw [← map_mul, ← map_one φ] at hx1
    exact φ.injective hx1
  have := congrArg (fun y : ↥(P : Subgroup ↥L) => ((y : ↥L) : H₁)) hx
  simpa using this

theorem kleinFix_map_mem {H₁ : Type} [Group H₁] {L : Subgroup H₁} [L.Normal] [IsSimpleGroup ↥L]
    {S : Subgroup H₁} (hSL : S ≤ L) (hS : S ≠ ⊥) (ψ : MulAut H₁) (hψ : ∀ x, ψ (ψ x) = x)
    (hψS : ∀ s ∈ S, ψ s = s) : ∀ x ∈ L, ψ x ∈ L := by
  have hnorm : (L.map ψ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance ψ.toMonoidHom ψ.surjective
  have : ((L.map ψ.toMonoidHom).subgroupOf L).Normal := hnorm.subgroupOf L
  rcases Subgroup.Normal.eq_bot_or_eq_top ((L.map ψ.toMonoidHom).subgroupOf L) with hbot | htop
  · exfalso
    apply hS
    rw [eq_bot_iff]
    intro s hs
    have hsL : s ∈ L := hSL hs
    have hmem : (⟨s, hsL⟩ : ↥L) ∈ (L.map ψ.toMonoidHom).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨s, hsL, hψS s hs⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : s = 1 := congrArg Subtype.val hmem
    rw [h1]
    exact Subgroup.one_mem _
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥L) ∈ (L.map ψ.toMonoidHom).subgroupOf L := by
      rw [htop]
      trivial
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : ψ y = x := hyx
    rw [← hyx', hψ y]
    exact hy

theorem klein_fixing_involution_inner {H₁ : Type} [Group H₁] [Finite H₁]
    (S : Subgroup H₁) (hS4 : Nat.card ↥S = 4) (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (L : Subgroup H₁) [L.Normal] (hSL : S ≤ L)
    {F : Type} [Field F] [Finite F] (hF : CFSG.GH74.GLS.IVK.L2Field F)
    (eL : ↥L ≃* CFSG.GH74.GLS.IVK.L2 F)
    (hL2 : (Nat.card ↥L).factorization 2 = 2)
    (ψ : MulAut H₁) (hψ : ∀ x, ψ (ψ x) = x) (hψS : ∀ s ∈ S, ψ s = s) :
    ∃ s₀ ∈ S, ∀ x ∈ L, ψ x = s₀ * x * s₀⁻¹ := by
  have : IsSimpleGroup ↥L := kleinFix_isSimpleGroup hF eL
  have hcen : Subgroup.center ↥L = ⊥ := kleinFix_center_eq_bot eL
  have hS1 : ∀ s ∈ S, s * s = 1 := kleinFix_sq_eq_one hF eL hL2 hS4 hSL
  have hSbot : S ≠ ⊥ := by
    intro h
    rw [h] at hS4
    simp at hS4
  have hψL : ∀ x ∈ L, ψ x ∈ L := kleinFix_map_mem hSL hSbot ψ hψ hψS
  obtain ⟨α, hα⟩ : ∃ α : MulAut ↥L, ∀ x : ↥L, (α x : H₁) = ψ x :=
    ⟨{ toFun := fun x => ⟨ψ (x : H₁), hψL x x.2⟩
       invFun := fun x => ⟨ψ (x : H₁), hψL x x.2⟩
       left_inv := fun x => Subtype.ext (hψ x)
       right_inv := fun x => Subtype.ext (hψ x)
       map_mul' := fun x y => Subtype.ext (map_mul ψ (x : H₁) (y : H₁)) }, fun _ => rfl⟩
  let φ : ↥S →* MulAut ↥L := (MulAut.conjNormal : H₁ →* MulAut ↥L).comp S.subtype
  have hφ : ∀ (s : ↥S) (x : ↥L), ((φ s x : ↥L) : H₁) = s * x * (s : H₁)⁻¹ := fun s x =>
    MulAut.conjNormal_apply (s : H₁) x
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsL : (s : H₁) ∈ L := hSL s.2
    have hmem : (⟨(s : H₁), hsL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have h1 := hφ s g
      rw [hs] at h1
      have h2 : (g : H₁) = s * g * (s : H₁)⁻¹ := h1
      show (g : H₁) * s = s * g
      calc (g : H₁) * s = (s * g * (s : H₁)⁻¹) * s := by rw [← h2]
        _ = s * g := by group
    rw [hcen, Subgroup.mem_bot] at hmem
    have h1 : (s : H₁) = 1 := congrArg Subtype.val hmem
    exact Subtype.ext h1
  have hαα : α * α = 1 := by
    ext x
    show ((α (α x) : ↥L) : H₁) = x
    rw [hα, hα]
    exact hψ x
  have hαφ : ∀ s : ↥S, φ s * α = α * φ s := by
    intro s
    ext x
    show ((φ s (α x) : ↥L) : H₁) = ((α (φ s x) : ↥L) : H₁)
    rw [hφ, hα, hα, hφ, map_mul, map_mul, hψS s s.2, map_inv, hψS s s.2]
  by_cases hmem : α ∈ φ.range
  · obtain ⟨s, hs⟩ := hmem
    refine ⟨s, s.2, fun x hx => ?_⟩
    have h1 := hα ⟨x, hx⟩
    rw [← hs, hφ] at h1
    exact h1.symm
  · exfalso
    have hB4 : Nat.card φ.range = 4 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hS4]
    have hBc : ∀ b ∈ φ.range, ∀ c ∈ φ.range, b * c = c * b := by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hSc s s.2 t t.2)
    have hBsq : ∀ b ∈ φ.range, b * b = 1 := by
      rintro _ ⟨s, rfl⟩
      have h1 : s * s = 1 := Subtype.ext (hS1 s s.2)
      rw [← map_mul, h1, map_one]
    have hBα : ∀ b ∈ φ.range, b * α = α * b := by
      rintro _ ⟨s, rfl⟩
      exact hαφ s
    obtain ⟨E, hE8, hEc, hEsq⟩ := kleinFix_exists_elemAbelian_eight φ.range hB4 hBc hBsq hαα hmem hBα
    exact kleinFix_not_elemAbelian_eight eL hF hL2 E hE8 hEc hEsq

end CbarE

end CFSG.GH74.GLS.LU.Local.Five
