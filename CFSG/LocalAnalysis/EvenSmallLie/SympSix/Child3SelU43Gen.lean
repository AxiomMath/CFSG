module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU33
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Arr
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup

theorem GL3_pow_cases (g : GL (Fin 3) (ZMod 2)) : g ^ 4 = 1 ∨ g ^ 6 = 1 ∨ g ^ 14 = 1 := by
  have key : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det ≠ 0 →
      M ^ 4 = 1 ∨ M ^ 6 = 1 ∨ M ^ 14 = 1 := by
    decide +kernel
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hu : ∀ k : ℕ, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ k = 1 → g ^ k = 1 := fun k h =>
    Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  rcases key _ hdet with h | h | h
  · exact Or.inl (hu 4 h)
  · exact Or.inr (Or.inl (hu 6 h))
  · exact Or.inr (Or.inr (hu 14 h))

@[expose] def invSup {Y : Type*} [Group Y] {a : Y} (ha : a ^ 2 = 1) {J : Subgroup Y}
    (hJa : J ≤ centralizer {a}) : Subgroup Y where
  carrier := {y | y ∈ J ∨ a * y ∈ J}
  one_mem' := Or.inl J.one_mem
  mul_mem' := by
    have hai : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, ha]
    have hc : ∀ j ∈ J, a * j = j * a := fun j hj => (mem_centralizer_singleton_iff.1 (hJa hj)).symm
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (J.mul_mem hx hy)
    · refine Or.inr ?_
      rw [← mul_assoc, hc x hx, mul_assoc]
      exact J.mul_mem hx hy
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact J.mul_mem hx hy
    · refine Or.inl ?_
      have e : x * y = (a * x) * (a * y) := by
        rw [← mul_assoc (a * x) a y, ← hc _ hx, ← mul_assoc a a x, ← sq, ha, one_mul]
      rw [e]
      exact J.mul_mem hx hy
  inv_mem' := by
    have hai : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq, ha]
    have hc : ∀ j ∈ J, a * j = j * a := fun j hj => (mem_centralizer_singleton_iff.1 (hJa hj)).symm
    rintro x (hx | hx)
    · exact Or.inl (J.inv_mem hx)
    · refine Or.inr ?_
      set j := a * x with hj
      have hxj : x = a * j := by rw [hj, ← mul_assoc, ← sq, ha, one_mul]
      have e : a * x⁻¹ = j⁻¹ := by
        rw [hxj, mul_inv_rev, hai, ← mul_assoc, hc _ (J.inv_mem hx), mul_assoc, ← sq, ha, mul_one]
      rw [e]
      exact J.inv_mem hx

theorem pow_cases_of_mem_sup {Y : Type*} [Group Y] {a : Y} (ha : a ^ 2 = 1) {J : Subgroup Y}
    (hJa : J ≤ centralizer {a}) (ψ : J ≃* GL (Fin 3) (ZMod 2)) {y : Y}
    (hy : y ∈ zpowers a ⊔ J) : y ^ 4 = 1 ∨ y ^ 6 = 1 ∨ y ^ 14 = 1 := by
  have hle : zpowers a ⊔ J ≤ invSup ha hJa := by
    refine sup_le ?_ fun j hj => Or.inl hj
    rw [zpowers_le]
    exact Or.inr (by rw [← sq, ha]; exact J.one_mem)
  have hjp : ∀ j ∈ J, j ^ 4 = 1 ∨ j ^ 6 = 1 ∨ j ^ 14 = 1 := by
    intro j hj
    have hp : ∀ k : ℕ, ψ ⟨j, hj⟩ ^ k = 1 → j ^ k = 1 := fun k h => by
      have h1 : (⟨j, hj⟩ : J) ^ k = 1 := ψ.injective (by rw [map_pow, h, map_one])
      have h2 := congrArg Subtype.val h1
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rcases GL3_pow_cases (ψ ⟨j, hj⟩) with h | h | h
    · exact Or.inl (hp 4 h)
    · exact Or.inr (Or.inl (hp 6 h))
    · exact Or.inr (Or.inr (hp 14 h))
  rcases hle hy with h | h
  · exact hjp y h
  · set j := a * y with hj
    have hyj : y = a * j := by rw [hj, ← mul_assoc, ← sq, ha, one_mul]
    have hcomm : Commute a j := (mem_centralizer_singleton_iff.1 (hJa h)).symm
    have hev : ∀ m : ℕ, Even m → y ^ m = j ^ m := by
      rintro m ⟨k, rfl⟩
      rw [hyj, hcomm.mul_pow, ← two_mul, pow_mul, ha, one_pow, one_mul]
    rcases hjp j h with h' | h' | h'
    · exact Or.inl (by rw [hev 4 (by decide), h'])
    · exact Or.inr (Or.inl (by rw [hev 6 (by decide), h']))
    · exact Or.inr (Or.inr (by rw [hev 14 (by decide), h']))

theorem false_of_autModel_witness {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hC : centralizer {a} = zpowers a ⊔ J) (ψ : J ≃* GL (Fin 3) (ZMod 2)) {G : Type*}
    [Group G] (M : CFSG.GH74.KGroups.AutModel D G)
    (hwit : ∀ τ ∈ M.A, orderOf τ = 2 →
      ∃ w ∈ M.P, w * τ = τ * w ∧ w ^ 4 ≠ 1 ∧ w ^ 6 ≠ 1 ∧ w ^ 14 ≠ 1) : False := by
  have ha2 : a ^ 2 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hJa : J ≤ centralizer {a} := hC ▸ le_sup_right
  set α := srcAut D a
  set τ : G := ((M.Φ α : M.A) : G)
  have hτ2 : τ ^ 2 = 1 := by rw [← M.Φ_pow, srcAut_sq ha, M.Φ_one]
  have hτ1 : τ ≠ 1 := fun h => srcAut_ne_one hCD ha (M.Φ_eq_one.1 h)
  have hτ : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
  obtain ⟨w, hwP, hwc, h4, h6, h14⟩ := hwit τ (M.Φ α).2 hτ
  set x : D := M.e.symm ⟨w, hwP⟩
  have hex : ((M.e x : M.P) : G) = w := by simp [x]
  have hfix : α x = x := by
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec α x, hex]
    calc τ * w * τ⁻¹ = w * τ * τ⁻¹ := by rw [hwc]
      _ = w := by group
  have hxa : (x : Y) ∈ centralizer {a} := by
    rw [mem_centralizer_singleton_iff]
    have h1 := srcAut_apply D a x
    rw [hfix] at h1
    calc (x : Y) * a = (a * x * a⁻¹) * a := by rw [← h1]
      _ = a * x := by group
  rw [hC] at hxa
  have hpow : ∀ k : ℕ, (x : Y) ^ k = 1 → w ^ k = 1 := fun k h => by
    have h1 : x ^ k = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, h, OneMemClass.coe_one])
    rw [← hex, ← SubgroupClass.coe_pow, ← map_pow, h1, map_one, OneMemClass.coe_one]
  rcases pow_cases_of_mem_sup ha2 hJa ψ hxa with h | h | h
  · exact h4 (hpow 4 h)
  · exact h6 (hpow 6 h)
  · exact h14 (hpow 14 h)

@[expose] def IsWit {G : Type*} [Group G] (T : Subgroup G) (τ w : G) : Prop :=
  w ∈ T ∧ w * τ = τ * w ∧ w ^ 4 ≠ 1 ∧ w ^ 6 ≠ 1 ∧ w ^ 14 ≠ 1

theorem IsWit.conj {G : Type*} [Group G] {T : Subgroup G} {τ w : G} (h : IsWit T τ w) {g : G}
    (hg : g * w * g⁻¹ ∈ T) : IsWit T (g * τ * g⁻¹) (g * w * g⁻¹) := by
  obtain ⟨-, hc, h4, h6, h14⟩ := h
  refine ⟨hg, ?_, ?_, ?_, ?_⟩
  · calc g * w * g⁻¹ * (g * τ * g⁻¹) = g * (w * τ) * g⁻¹ := by group
      _ = g * (τ * w) * g⁻¹ := by rw [hc]
      _ = g * τ * g⁻¹ * (g * w * g⁻¹) := by group
  · rwa [conj_pow, Ne, conj_eq_one_iff]
  · rwa [conj_pow, Ne, conj_eq_one_iff]
  · rwa [conj_pow, Ne, conj_eq_one_iff]

theorem forall_witness_of_reps {G : Type*} [Group G] {A T S : Subgroup G}
    (hTA : ∀ g ∈ A, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hSA : S ≤ A)
    (hsyl : ∀ τ ∈ A, orderOf τ = 2 → ∃ g ∈ A, g * τ * g⁻¹ ∈ S) (r : ℕ) (y : ℕ → G)
    (hrep : ∀ u ∈ S, orderOf u = 2 → ∃ j < r, ∃ c ∈ S, u = c * y j * c⁻¹)
    (hwj : ∀ j < r, ∃ w, IsWit T (y j) w) :
    ∀ τ ∈ A, orderOf τ = 2 → ∃ w, IsWit T τ w := by
  intro τ hτA hτ
  obtain ⟨g, hgA, hgS⟩ := hsyl τ hτA hτ
  have ho : orderOf (g * τ * g⁻¹) = 2 := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ]
  obtain ⟨j, hj, c, hcS, hu⟩ := hrep _ hgS ho
  obtain ⟨w, hw⟩ := hwj j hj
  set h := g⁻¹ * c
  have hhA : h ∈ A := A.mul_mem (A.inv_mem hgA) (hSA hcS)
  have hτh : τ = h * y j * h⁻¹ := by
    have e : τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
    rw [e, hu]
    simp only [h, mul_inv_rev, inv_inv]
    group
  refine ⟨h * w * h⁻¹, ?_⟩
  rw [hτh]
  exact hw.conj (hTA h hhA w hw.1)

theorem exists_conj_mem_of_index {G : Type*} [Group G] {A S : Subgroup G} [Finite A]
    (hSA : S ≤ A) {k : ℕ} (hS : Nat.card S = 2 ^ k) (hidx : ¬ 2 ∣ (S.subgroupOf A).index) :
    ∀ τ ∈ A, orderOf τ = 2 → ∃ g ∈ A, g * τ * g⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro τ hτA hτ
  have hcard : Nat.card (S.subgroupOf A) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv, hS]
  set P : Sylow 2 A := (IsPGroup.of_card hcard).toSylow hidx
  have hP : (P : Subgroup A) = S.subgroupOf A := IsPGroup.toSylow_coe _ hidx
  set τ' : A := ⟨τ, hτA⟩
  have hX : IsPGroup 2 (zpowers τ') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hτ, pow_one])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A Q P
  have h1 : g * τ' * g⁻¹ ∈ (P : Subgroup A) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply]
    have : g⁻¹ * (g * τ' * g⁻¹) * g = τ' := by group
    rw [this]
    exact hQ (mem_zpowers τ')
  rw [hP, mem_subgroupOf] at h1
  exact ⟨g, g.2, by simpa using h1⟩

theorem le_normalizer_of_conj_gens {G : Type*} [Group G] {T A : Subgroup G} [Finite T]
    {gT gA : Set G} (hT : T = closure gT) (hA : A = closure gA)
    (h : ∀ g ∈ gA, ∀ x ∈ gT, g * x * g⁻¹ ∈ T) : A ≤ normalizer (T : Set G) := by
  rw [hA, closure_le]
  intro g hg
  refine CFSG.GH74.KGroups.mem_normalizer_of_conj_mem T g fun x hx => ?_
  have hle : T ≤ T.comap (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [hT]
    rw [closure_le]
    intro x hx
    exact h g hg x hx
  exact hle hx

theorem eq_one_of_forall_comm {n : ℕ} {T : Subgroup (Equiv.Perm (Fin n))}
    {c : Equiv.Perm (Fin n)} (hc : ∀ g ∈ T, g * c = c * g)
    (hroot : ∀ p : Fin n, ∃ r : Fin n, (∃ g ∈ T, g r = p) ∧
      ∀ q : Fin n, q ≠ r → ∃ s ∈ T, s r = r ∧ s q ≠ q) : c = 1 := by
  refine Equiv.ext fun p => ?_
  obtain ⟨r, ⟨g, hg, rfl⟩, hst⟩ := hroot p
  have hcr : c r = r := by
    by_contra hne
    obtain ⟨s, hs, hsr, hsq⟩ := hst (c r) hne
    apply hsq
    have := congrArg (fun f : Equiv.Perm (Fin n) => f r) (hc s hs)
    simp only [Equiv.Perm.mul_apply, hsr] at this
    exact this
  have := congrArg (fun f : Equiv.Perm (Fin n) => f r) (hc g hg)
  simp only [Equiv.Perm.mul_apply, hcr] at this
  rw [Equiv.Perm.one_apply, ← this]

section Arrays

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {n : ℕ}

theorem rep_powN {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    ∀ k : ℕ, Rep n (powN n t k) (g ^ k)
  | 0 => by rw [pow_zero]; exact rep_idA
  | k + 1 => by rw [powN, pow_succ']; exact rep_compA h (rep_powN h k)

theorem rep_conjA {g x : Array ℕ} {G X : Equiv.Perm (Fin n)} (hg : Rep n g G) (hx : Rep n x X)
    (hi : isInvA n g (invCand n g) = true) : Rep n (conjA n g x) (G * X * G⁻¹) :=
  rep_compA (rep_compA hg hx) (rep_inv_of_isInvA hg hi)

theorem witOK_spec {y w : Array ℕ} {Y W : Equiv.Perm (Fin n)} (hy : Rep n y Y) (hw : Rep n w W)
    (h : witOK n y w = true) : W * Y = Y * W ∧ W ^ 4 ≠ 1 ∧ W ^ 6 ≠ 1 ∧ W ^ 14 ≠ 1 := by
  simp only [witOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨eq_of_eqA (rep_compA hw hy) (rep_compA hy hw) h1, fun he => ?_, fun he => ?_,
    fun he => ?_⟩
  · rw [(eqA_iff (rep_powN hw 4) rep_idA).2 he] at h2
    exact Bool.noConfusion h2
  · rw [(eqA_iff (rep_powN hw 6) rep_idA).2 he] at h3
    exact Bool.noConfusion h3
  · rw [(eqA_iff (rep_powN hw 14) rep_idA).2 he] at h4
    exact Bool.noConfusion h4

theorem exists_rep_word {T : Subgroup (Equiv.Perm (Fin n))} {S : Array (Array ℕ)}
    (hS : ∀ h < S.size, Rep n S[h]! (permOfArr n S[h]!) ∧
      Rep n (rawInvs n S)[h]! (permOfArr n S[h]!)⁻¹ ∧ permOfArr n S[h]! ∈ T)
    {w : List ℤ} (hw : lettersOK S.size w = true) :
    ∃ g ∈ T, Rep n (wordA n S (rawInvs n S) w) g :=
  CFSG.EvenSmallLie.OmegaEight.wordA_mem' hS w hw

theorem eq_one_of_centOK {T : Subgroup (Equiv.Perm (Fin n))} {S : Array (Array ℕ)}
    (hS : ∀ h < S.size, Rep n S[h]! (permOfArr n S[h]!) ∧
      Rep n (rawInvs n S)[h]! (permOfArr n S[h]!)⁻¹ ∧ permOfArr n S[h]! ∈ T)
    {rs : List (ℕ × List (List ℤ))} (hok : centOK n S rs = true) {c : Equiv.Perm (Fin n)}
    (hc : ∀ g ∈ T, g * c = c * g) : c = 1 := by
  simp only [centOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨hst, hfor⟩ := hok
  set F := bfsForest n S (rs.map Prod.fst)
  have hreach : ∀ d : ℕ, ∀ p : ℕ, ∀ hp : p < n, F.2.2[p]! = d →
      ∃ r ∈ rs, ∃ hr : r.1 < n, ∃ g ∈ T, g ⟨r.1, hr⟩ = ⟨p, hp⟩ := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp hd
      have hf := allLt_spec hfor hp
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.contains_iff_mem, List.mem_map] at hf
      rcases hf with ⟨-, r, hr, rfl⟩ | ⟨⟨⟨hpar, hlab⟩, hdep⟩, hstep⟩
      · exact ⟨r, hr, hp, 1, T.one_mem, rfl⟩
      · obtain ⟨r, hr, hrn, g, hg, hgr⟩ := ih _ (hd ▸ hdep) _ hpar rfl
        refine ⟨r, hr, hrn, permOfArr n S[F.2.1[p]!]! * g, T.mul_mem (hS _ hlab).2.2 hg, ?_⟩
        rw [Equiv.Perm.mul_apply, hgr]
        apply Fin.ext
        rw [← (hS _ hlab).1.apply hpar, hstep]
  refine eq_one_of_forall_comm hc fun p => ?_
  obtain ⟨r, hr, hrn, g, hg, hgr⟩ := hreach _ p p.2 rfl
  refine ⟨⟨r.1, hrn⟩, ⟨g, hg, hgr⟩, fun q hq => ?_⟩
  have h1 := hst r hr
  simp only [stabOK, Bool.and_eq_true, List.all_eq_true, List.all_map, Function.comp_apply,
    beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨-, hlet⟩, hfix⟩, hmove⟩ := h1
  have hq' : (q : ℕ) ≠ r.1 := fun h => hq (Fin.ext h)
  have hm := allLt_spec hmove q.2
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_map, List.any_eq_true, Function.comp_apply,
    bne_iff_ne, ne_eq] at hm
  rcases hm with h | ⟨w, hw, hwq⟩
  · exact absurd h hq'
  obtain ⟨s, hs, hrep⟩ := exists_rep_word hS (hlet w hw)
  refine ⟨s, hs, Fin.ext ?_, fun h => hwq ?_⟩
  · rw [← hrep.apply hrn]
    exact hfix w hw
  · rw [hrep.apply q.2, h]

end Arrays

end CFSG.EvenSmallLie.Child3
