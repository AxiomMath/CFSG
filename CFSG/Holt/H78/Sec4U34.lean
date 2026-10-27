module

public import CFSG.Holt.H78.Sec4SEAutFix

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Unitary

variable {Δ : Type} [Finite Δ] {L : Subgroup (Equiv.Perm Δ)} {n e : ℕ}

theorem exists_apply_eq_of_pow_two_pow_eq_one (hΔ : Odd (Nat.card Δ)) {s : Equiv.Perm Δ}
    {k : ℕ} (hs : s ^ 2 ^ k = 1) : ∃ b, s b = b := by
  classical
  have := Fintype.ofFinite Δ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_compl_support_modEq hs
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hΔ
  have hpos : 0 < s.supportᶜ.card := by
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  exact ⟨b, by simpa [Equiv.Perm.mem_support] using hb⟩

namespace IsBenderAction

theorem fixedBy_eq_insert_image_of_unitary (hA : IsBenderAction ↥L Δ n 3 e)
    {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hx2 : x * x = 1) (hxL : x ∉ L) {b c : Δ} (hcb : c ≠ b) (hxb : x b = b) (hxc : x c = c) :
    fixedBy Δ x = insert b ((fun z : Equiv.Perm Δ => z c) ''
      (rootCenter (seRadical L b) : Set (Equiv.Perm Δ))) := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  have hxc' : x⁻¹ c = c := by rw [Equiv.Perm.inv_eq_iff_eq, hxc]
  ext δ
  simp only [mem_fixedBy, Equiv.Perm.smul_def, Set.mem_insert_iff, Set.mem_image,
    SetLike.mem_coe]
  constructor
  · intro hδ
    by_cases hδb : δ = b
    · exact Or.inl hδb
    right
    obtain ⟨r, hr, hrc⟩ := hL.exists_mem_seRadical_apply_eq hcb hδb
    refine ⟨r, ?_, hrc⟩
    have h1 : r⁻¹ * (x * r * x⁻¹) ∈ seRadical L b :=
      mul_mem (inv_mem hr) (conj_mem_seRadical hx hxb hr)
    have h2 : (r⁻¹ * (x * r * x⁻¹)) c = c := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hxc', hrc, hδ,
        Equiv.Perm.inv_eq_iff_eq, hrc]
    have h3 := hL.eq_one_of_mem_seRadical h1 hcb h2
    have h4 : x * r = r * x := by
      calc x * r = r * (r⁻¹ * (x * r * x⁻¹)) * x := by group
        _ = r * x := by rw [h3, mul_one]
    exact (hA.commute_iff_mem_rootCenter_of_unitary hx hx2 hxL hxb hr).mp h4
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact hxb
    · have h := (hA.commute_iff_mem_rootCenter_of_unitary hx hx2 hxL hxb hz.1).mpr hz
      have h' := congrArg (fun π : Equiv.Perm Δ => π c) h
      simp only [Equiv.Perm.mul_apply, hxc] at h'
      exact h'

theorem ncard_fixedBy_of_unitary (hA : IsBenderAction ↥L Δ n 3 e) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx2 : x * x = 1) (hxL : x ∉ L) :
    (fixedBy Δ x).ncard = 2 ^ n + 1 := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  obtain ⟨b, c, hbc, hxb, hxc⟩ := hL.exists_ne_fixed hx hx2 hxL
  rw [hA.fixedBy_eq_insert_image_of_unitary hx hx2 hxL (Ne.symm hbc) hxb hxc]
  have hnot : b ∉ (fun z : Equiv.Perm Δ => z c) ''
      (rootCenter (seRadical L b) : Set (Equiv.Perm Δ)) := by
    rintro ⟨z, hz, hzc⟩
    have hzb : z b = b := apply_eq_of_mem_seRadical hz.1
    exact hbc (z.injective (hzb.trans hzc.symm))
  have hinj : Set.InjOn (fun z : Equiv.Perm Δ => z c)
      (rootCenter (seRadical L b) : Set (Equiv.Perm Δ)) := by
    intro z₁ hz₁ z₂ hz₂ h12
    have h1 : z₂⁻¹ * z₁ ∈ seRadical L b := mul_mem (inv_mem hz₂.1) hz₁.1
    have h2 : (z₂⁻¹ * z₁) c = c := by
      simp only at h12
      rw [Equiv.Perm.mul_apply, h12]
      exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
    have h3 := hL.eq_one_of_mem_seRadical h1 (Ne.symm hbc) h2
    calc z₁ = z₂ * (z₂⁻¹ * z₁) := by group
      _ = z₂ := by rw [h3, mul_one]
  rw [Set.ncard_insert_of_notMem hnot, hinj.ncard_image, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, hA.card_rootCenter_seRadical]

theorem commute_of_forall_apply_eq (hA : IsBenderAction ↥L Δ n 3 e) {x y : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hy : y ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hy2 : y * y = 1) (hyL : y ∉ L)
    (hxy : ∀ δ, y δ = δ → x δ = δ) {b : Δ} (hyb : y b = b) {z : Equiv.Perm Δ}
    (hz : z ∈ rootCenter (seRadical L b)) : x * z = z * x := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  obtain ⟨c, hcb, hyc⟩ := hL.exists_ne_apply_eq hy hy2 hyL b
  have hxb := hxy b hyb
  have hxc' : x⁻¹ c = c := by rw [Equiv.Perm.inv_eq_iff_eq, hxy c hyc]
  have hyz : y * z = z * y :=
    (hA.commute_iff_mem_rootCenter_of_unitary hy hy2 hyL hyb hz.1).mpr hz
  have hyzc : y (z c) = z c := by
    have h := congrArg (fun π : Equiv.Perm Δ => π c) hyz
    simp only [Equiv.Perm.mul_apply, hyc] at h
    exact h
  have hxzc : x (z c) = z c := hxy _ hyzc
  have h1 : z⁻¹ * (x * z * x⁻¹) ∈ seRadical L b :=
    mul_mem (inv_mem hz.1) (conj_mem_rootCenter_seRadical hx hxb hz).1
  have h2 : (z⁻¹ * (x * z * x⁻¹)) c = c := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hxc', hxzc]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have h3 := hL.eq_one_of_mem_seRadical h1 hcb h2
  calc x * z = z * (z⁻¹ * (x * z * x⁻¹)) * x := by group
    _ = z * x := by rw [h3, mul_one]

theorem commute_of_forall_apply_eq_of_pow (hA : IsBenderAction ↥L Δ n 3 e)
    {x y : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hy : y ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hy2 : y * y = 1) (hyL : y ∉ L)
    (hxy : ∀ δ, y δ = δ → x δ = δ) {s : Equiv.Perm Δ} (hsL : s ∈ L) (hsy : y * s = s * y)
    {k : ℕ} (hs : s ^ 2 ^ k = 1) : x * s = s * x := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  obtain ⟨b, hsb⟩ := exists_apply_eq_of_pow_two_pow_eq_one hA.odd_card hs
  have hsR : s ∈ seRadical L b := mem_seRadical_of_pow_eq_one hsL hsb hs
  by_cases hyb : y b = b
  · exact hA.commute_of_forall_apply_eq hx hy hy2 hyL hxy hyb
      ((hA.commute_iff_mem_rootCenter_of_unitary hy hy2 hyL hyb hsR).mp hsy)
  · have hsyb : s (y b) = y b := by
      have h := congrArg (fun π : Equiv.Perm Δ => π b) hsy
      simp only [Equiv.Perm.mul_apply, hsb] at h
      exact h.symm
    rw [hL.eq_one_of_mem_seRadical hsR hyb hsyb, mul_one, one_mul]

theorem commute_of_forall_apply_eq_of_commute (hA : IsBenderAction ↥L Δ n 3 e)
    {x y : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hy : y ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hy2 : y * y = 1) (hyL : y ∉ L)
    (hxy : ∀ δ, y δ = δ → x δ = δ) {c : Equiv.Perm Δ} (hcL : c ∈ L) (hcy : y * c = c * y) :
    x * c = c * x := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  set α := L.normalizerMonoidHom ⟨y, hy⟩ with hαdef
  have hα2 : α * α = 1 := normalizerMonoidHom_mul_self hy hy2
  have hαout := hL.not_inner hy hyL
  have hmem : ∀ g : ↥L, g ∈ autFixed α ↔ y * g = g * y := by
    intro g
    change α g = g ↔ _
    rw [← Subtype.coe_inj, hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    constructor
    · intro h
      calc y * g = y * g * y⁻¹ * y := by group
        _ = g * y := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  obtain ⟨φ⟩ := hA.benderType.fixed_unitary α hα2 hαout
  have hn : 2 ≤ n := hA.params.2.2
  have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv _ φ.toEquiv
  have : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model n) :=
    (BenderType.linear n hn (MulEquiv.refl _)).isSimple
  have : IsSimpleGroup (autFixed α) := φ.isSimpleGroup
  let S : Set (autFixed α) := {g | ∃ k : ℕ, g ^ 2 ^ k = 1}
  let Z : Subgroup (autFixed α) :=
    (Subgroup.centralizer {x}).comap (L.subtype.comp (autFixed α).subtype)
  have hZ : ∀ g : autFixed α, g ∈ Z ↔ x * ((g : ↥L) : Equiv.Perm Δ) = (g : Equiv.Perm Δ) * x := by
    intro g
    simp only [Z, Subgroup.mem_comap, MonoidHom.coe_comp, Subgroup.coe_subtype,
      Function.comp_apply, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hSZ : Subgroup.normalClosure S ≤ Z := by
    show Subgroup.closure (Group.conjugatesOfSet S) ≤ Z
    refine (Subgroup.closure_le Z).mpr fun g hg => ?_
    obtain ⟨a, ⟨k, hak⟩, hag⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨u, rfl⟩ := isConj_iff.mp hag
    have hk : (u * a * u⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hak, mul_one, mul_inv_cancel]
    rw [SetLike.mem_coe, hZ]
    refine hA.commute_of_forall_apply_eq_of_pow hx hy hy2 hyL hxy
      ((u * a * u⁻¹ : autFixed α) : ↥L).2 ((hmem _).mp (u * a * u⁻¹).2) (k := k) ?_
    have h := congrArg (fun g : autFixed α => ((g : ↥L) : Equiv.Perm Δ)) hk
    simpa using h
  have hS1 : Subgroup.normalClosure S ≠ ⊥ := by
    obtain ⟨b, hyb⟩ := exists_apply_eq_of_pow_two_pow_eq_one hA.odd_card (k := 1)
      (by rw [pow_one, sq, hy2])
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ rootCenter (seRadical L b), z ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : rootCenter (seRadical L b) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
      have hcard := hA.card_rootCenter_seRadical b
      rw [hbot, Subgroup.card_bot] at hcard
      have := hA.four_le_q
      omega
    have hzL : z ∈ L := seRadical_le hz.1
    have hzy : y * z = z * y :=
      (hA.commute_iff_mem_rootCenter_of_unitary hy hy2 hyL hyb hz.1).mpr hz
    have hzC : (⟨z, hzL⟩ : ↥L) ∈ autFixed α := (hmem _).mpr hzy
    have hzz : z * z = 1 := hL.mul_self_eq_one_of_mem_rootCenter hz
    intro hbot
    have hzS : (⟨⟨z, hzL⟩, hzC⟩ : autFixed α) ∈ Subgroup.normalClosure S := by
      refine Subgroup.subset_normalClosure ⟨1, ?_⟩
      ext1
      ext1
      simp [sq, hzz]
    rw [hbot, Subgroup.mem_bot] at hzS
    apply hz1
    have h := congrArg (fun g : autFixed α => ((g : ↥L) : Equiv.Perm Δ)) hzS
    simpa using h
  have htop : Subgroup.normalClosure S = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure S)).resolve_left hS1
  have hcC : (⟨c, hcL⟩ : ↥L) ∈ autFixed α := (hmem _).mpr hcy
  have h := hSZ (htop ▸ Subgroup.mem_top (⟨⟨c, hcL⟩, hcC⟩ : autFixed α))
  exact (hZ _).mp h

theorem exists_apply_ne_of_unitary (hA : IsBenderAction ↥L Δ n 3 e) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hx4 : x ^ 4 = 1)
    (hx2L : x ^ 2 ∉ L) : ∃ δ, (x ^ 2) δ = δ ∧ x δ ≠ δ := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  have hy : x ^ 2 ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ)) := pow_mem hx 2
  have hy2 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hx4
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx2L (by rw [one_pow]; exact L.one_mem)
  by_contra hcon
  push Not at hcon
  set α := L.normalizerMonoidHom ⟨x ^ 2, hy⟩ with hαdef
  set β := L.normalizerMonoidHom ⟨x, hx⟩ with hβdef
  have hα2 : α * α = 1 := normalizerMonoidHom_mul_self hy hy2
  have hαout := hL.not_inner hy hx2L
  have hcomm : (⟨x, hx⟩ : Subgroup.normalizer (L : Set (Equiv.Perm Δ))) * ⟨x ^ 2, hy⟩ =
      ⟨x ^ 2, hy⟩ * ⟨x, hx⟩ := Subtype.ext (Commute.self_pow x 2).eq
  have hβα : β * α = α * β := by
    rw [hαdef, hβdef, ← map_mul, ← map_mul, hcomm]
  have hβ : ∀ g ∈ autFixed α, β g = g := by
    intro g hg
    have h : (α g : Equiv.Perm Δ) = g := congrArg Subtype.val hg
    rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    have hgy : x ^ 2 * g = g * x ^ 2 := by
      calc x ^ 2 * g = x ^ 2 * g * (x ^ 2)⁻¹ * x ^ 2 := by group
        _ = g * x ^ 2 := by rw [h]
    have hxg := hA.commute_of_forall_apply_eq_of_commute hx hy hy2 hx2L hcon g.2 hgy
    refine Subtype.ext ?_
    rw [hβdef, Subgroup.normalizerMonoidHom_apply_apply_coe, hxg, mul_inv_cancel_right]
  rcases hA.benderType.centralizer_unitary α hα2 hαout β hβα hβ with h1 | h1
  · refine hx1 (hL.eq_one_of_commute fun ℓ hℓ => ?_)
    have h := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨ℓ, hℓ⟩)
    rw [hβdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    calc x * ℓ = x * ℓ * x⁻¹ * x := by group
      _ = ℓ * x := by rw [h]; rfl
  · have h2 : (x ^ 2)⁻¹ * x = 1 := hL.eq_one_of_commute fun ℓ hℓ => by
      have h := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨ℓ, hℓ⟩)
      rw [hβdef, hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      calc (x ^ 2)⁻¹ * x * ℓ = (x ^ 2)⁻¹ * (x * ℓ * x⁻¹) * x := by group
        _ = ℓ * ((x ^ 2)⁻¹ * x) := by rw [h]; group
    have h3 : x ^ 2 = x := inv_mul_eq_one.mp h2
    refine hx1 ?_
    calc x = x⁻¹ * x ^ 2 := by group
      _ = 1 := by rw [h3, inv_mul_cancel]

theorem eq_one_of_mem_of_isPGroup (hA : IsBenderAction ↥L Δ n 3 e)
    {P : Subgroup (Equiv.Perm Δ)} (hP2 : IsPGroup 2 P) {a b : Δ} (hab : a ≠ b)
    (ha : a ∈ fixSet Δ P) (hb : b ∈ fixSet Δ P) {p : Equiv.Perm Δ} (hp : p ∈ P) (hpL : p ∈ L) :
    p = 1 := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
  have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact hL.eq_one_of_mem_seRadical (mem_seRadical_of_pow_eq_one hpL (ha p hp) hk') (Ne.symm hab)
    (hb p hp)

theorem card_eq_two_of_unitary (hA : IsBenderAction ↥L Δ n 3 e) {P : Subgroup (Equiv.Perm Δ)}
    (hP2 : IsPGroup 2 P) (hPN : P ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ)))
    (hP1 : P ≠ ⊥) (hF : 2 ^ n + 1 ≤ (fixSet Δ P).ncard) :
    Nat.card P = 2 ∧ (fixSet Δ P).ncard = 2 ^ n + 1 := by
  classical
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨n, 3, e, hA⟩
  have hq := hA.four_le_q
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Set.one_lt_ncard_iff (s := fixSet Δ P) (Set.toFinite _)).mp (by omega)
  have hPL : ∀ p ∈ P, p ∈ L → p = 1 := fun p hp hpL =>
    hA.eq_one_of_mem_of_isPGroup hP2 hab ha hb hp hpL
  by_cases hexp : ∀ p ∈ P, p * p = 1
  · obtain ⟨⟨y, hyP⟩, hy1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
    have hyL : y ∉ L := fun h => hy1 (hPL y hyP h)
    have huniq : ∀ p ∈ P, p = 1 ∨ p = y := by
      intro p hp
      by_cases hp1 : p = 1
      · exact Or.inl hp1
      · right
        have hpL : p ∉ L := fun h => hp1 (hPL p hp h)
        have h := hL.mul_inv_mem_of_isPGroup hP2 hPN hp hyP (hexp p hp) (hexp y hyP) hpL hyL
        exact mul_inv_eq_one.mp (hPL _ (mul_mem hp (inv_mem hyP)) h)
    have hPset : (P : Set (Equiv.Perm Δ)) = {1, y} := by
      ext p
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨huniq p, by rintro (rfl | rfl); exacts [P.one_mem, hyP]⟩
    have hfix : fixSet Δ P = fixedBy Δ y := by
      ext δ
      refine ⟨fun h => h y hyP, fun h p hp => ?_⟩
      rcases huniq p hp with rfl | rfl
      · exact one_smul _ δ
      · exact h
    refine ⟨?_, ?_⟩
    · rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hPset, Set.ncard_pair (Ne.symm hy1)]
    · rw [hfix]
      exact hA.ncard_fixedBy_of_unitary (hPN hyP) (hexp y hyP) hyL
  · push Not at hexp
    obtain ⟨p, hp, hpp⟩ := hexp
    obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
    have hex : ∃ i, p ^ 2 ^ i = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
    set i := Nat.find hex with hidef
    have hi : p ^ 2 ^ i = 1 := Nat.find_spec hex
    have hi2 : 2 ≤ i := by
      by_contra h
      have h2 : 2 ^ i ∣ 2 := by
        interval_cases i <;> norm_num
      obtain ⟨m, hm⟩ := h2
      exact hpp (by rw [← sq, hm, pow_mul, hi, one_pow])
    set x := p ^ 2 ^ (i - 2) with hxdef
    have hxpow : ∀ j, x ^ 2 ^ j = p ^ 2 ^ (i - 2 + j) := fun j => by
      rw [hxdef, ← pow_mul, ← pow_add]
    have hx4 : x ^ 4 = 1 := by
      have h := hxpow 2
      rw [show i - 2 + 2 = i by omega, hi] at h
      simpa using h
    have hx2 : x ^ 2 ≠ 1 := by
      have h := hxpow 1
      rw [pow_one] at h
      rw [h]
      exact Nat.find_min hex (by omega : i - 2 + 1 < i)
    have hxP : x ∈ P := pow_mem hp _
    have hx2P : x ^ 2 ∈ P := pow_mem hxP 2
    have hx2L : x ^ 2 ∉ L := fun h => hx2 (hPL _ hx2P h)
    obtain ⟨δ, hδ2, hδ⟩ := hA.exists_apply_ne_of_unitary (hPN hxP) hx4 hx2L
    have hy2 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hx4
    have hcard := hA.ncard_fixedBy_of_unitary (hPN hx2P) hy2 hx2L
    have hsub : fixSet Δ P ⊆ fixedBy Δ (x ^ 2) := fun δ h => h _ hx2P
    have heq : fixSet Δ P = fixedBy Δ (x ^ 2) :=
      Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
    have hδP : δ ∈ fixSet Δ P := by
      rw [heq]
      exact hδ2
    exact absurd (hδP x hxP) hδ

omit [Finite Δ] in
theorem card_outer_of_unitary_four (hA : IsBenderAction ↥L Δ 2 3 e) :
    Nat.card (Outer ↥L) = 4 := by
  obtain ⟨Dd, hDd, -, hcard, -, hq⟩ := hA.benderType.outer_unitary
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Dd, hq, hcard]
  norm_num

theorem mem_of_pow_three_pow_eq_one (hA : IsBenderAction ↥L Δ 2 3 e) {x : Equiv.Perm Δ}
    (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) {k : ℕ} (hxk : x ^ 3 ^ k = 1) :
    x ∈ L := by
  have hL : IsNaturalSE L := isNaturalSE_iff.mpr ⟨2, 3, e, hA⟩
  rw [← hL.normalizerOuterHom_eq_one_iff ⟨x, hx⟩]
  have h1 : normalizerOuterHom L ⟨x, hx⟩ ^ 3 ^ k = 1 := by
    rw [← map_pow]
    convert map_one (normalizerOuterHom L)
    exact Subtype.ext (by simpa using hxk)
  have h2 : normalizerOuterHom L ⟨x, hx⟩ ^ 4 = 1 := by
    have h := pow_card_eq_one' (x := normalizerOuterHom L ⟨x, hx⟩)
    rwa [hA.card_outer_of_unitary_four] at h
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at h3
  exact h3

theorem ncard_fixedBy_eq_two_of_mem (hA : IsBenderAction ↥L Δ 2 3 e) {x : Equiv.Perm Δ}
    (hxL : x ∈ L) {k : ℕ} (hxk : x ^ 3 ^ k = 1) (hx1 : x ≠ 1) : (fixedBy Δ x).ncard = 2 := by
  classical
  have := Fintype.ofFinite Δ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he : e = 5 := by
    rcases hA.benderType.cases' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · rw [he]
      norm_num
  subst he
  have hcard : Fintype.card Δ = 65 := by
    rw [← Nat.card_eq_fintype_card, hA.card_eq]
    norm_num
  have hmod := Equiv.Perm.card_compl_support_modEq hxk
  have hset : fixedBy Δ x = ↑(x.supportᶜ) := by
    ext δ
    simp [Equiv.Perm.mem_support, Equiv.Perm.smul_def]
  rw [hset, Set.ncard_coe_finset]
  have h2 : 1 < x.supportᶜ.card := by
    unfold Nat.ModEq at hmod
    rw [hcard] at hmod
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  have hxa : x a = a := by simpa [Equiv.Perm.mem_support] using ha
  have hxb : x b = b := by simpa [Equiv.Perm.mem_support] using hb
  have hx'D : (⟨x, hxL⟩ : ↥L) ∈ stabilizer ↥L a ⊓ stabilizer ↥L b := ⟨hxa, hxb⟩
  obtain ⟨t, ht, hta⟩ := hA.exists_involution_smul_eq hab
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  obtain ⟨-, hN1card, -, -, -, -, hDeq, -⟩ := hA.stabilizer_inf_decomposition hQ hab ht hta
  have hN1D := le_sup_left.trans hDeq.ge
  have : IsCyclic ↥(stabilizer ↥L a ⊓ stabilizer ↥L b) := hA.isCyclic_stabilizer_inf hab
  have hDcard := hA.card_stabilizer_inf hab
  set x' : ↥(stabilizer ↥L a ⊓ stabilizer ↥L b) := ⟨⟨x, hxL⟩, hx'D⟩ with hx'def
  have hord : orderOf x' = 3 := by
    have h15 := orderOf_dvd_natCard x'
    rw [hDcard, hx'def, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h15
    rw [hx'def, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    obtain ⟨j, -, hjeq⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hxk)
    rw [hjeq] at h15 ⊢
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by rw [hjeq, pow_zero]))
    have hj2 : j < 2 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ (2 ^ 2 - 1) * 5 := (pow_dvd_pow 3 (by omega)).trans h15
      norm_num at h9
    rw [show j = 1 by omega, pow_one]
  have hzeq : Subgroup.zpowers x' =
      (⁅stabilizer ↥L a ⊓ stabilizer ↥L b, Subgroup.zpowers t⁆).subgroupOf
        (stabilizer ↥L a ⊓ stabilizer ↥L b) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, hord,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN1D).toEquiv, hN1card]
    norm_num
  have hx'N : (⟨x, hxL⟩ : ↥L) ∈ ⁅stabilizer ↥L a ⊓ stabilizer ↥L b, Subgroup.zpowers t⁆ := by
    have h : x' ∈ (⁅stabilizer ↥L a ⊓ stabilizer ↥L b, Subgroup.zpowers t⁆).subgroupOf
        (stabilizer ↥L a ⊓ stabilizer ↥L b) := hzeq ▸ Subgroup.mem_zpowers x'
    exact Subgroup.mem_subgroupOf.mp h
  have hsub : x.supportᶜ = {a, b} := by
    ext γ
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hγ
      by_contra hne
      push Not at hne
      have h := hA.eq_one_of_mem_commutator_of_smul_eq hab ht hta hx'N hne.1 hne.2 hγ
      exact hx1 (congrArg Subtype.val h)
    · rintro (rfl | rfl)
      · exact hxa
      · exact hxb
  rw [hsub, Finset.card_pair hab]

theorem ncard_fixedBy_eq_two_of_unitary_four (hA : IsBenderAction ↥L Δ 2 3 e)
    {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) {k : ℕ}
    (hxk : x ^ 3 ^ k = 1) (hx1 : x ≠ 1) : x ∈ L ∧ (fixedBy Δ x).ncard = 2 :=
  ⟨hA.mem_of_pow_three_pow_eq_one hx hxk,
    hA.ncard_fixedBy_eq_two_of_mem (hA.mem_of_pow_three_pow_eq_one hx hxk) hxk hx1⟩

theorem eq_one_of_pow_three_pow_eq_one_of_fix_three (hA : IsBenderAction ↥L Δ 2 3 e)
    {x : Equiv.Perm Δ} (hx : x ∈ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) {k : ℕ}
    (hxk : x ^ 3 ^ k = 1) {a b c : Δ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : x a = a) (hxb : x b = b) (hxc : x c = c) : x = 1 := by
  by_contra hx1
  have h := (hA.ncard_fixedBy_eq_two_of_unitary_four hx hxk hx1).2
  have h3 : ({a, b, c} : Set Δ).ncard ≤ (fixedBy Δ x).ncard := by
    refine Set.ncard_le_ncard (fun δ hδ => ?_) (Set.toFinite _)
    rcases hδ with rfl | rfl | rfl
    · exact hxa
    · exact hxb
    · exact hxc
  rw [Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩, h] at h3
  omega

theorem card_eq_two_of_unitary_four (hA : IsBenderAction ↥L Δ 2 3 e)
    {P : Subgroup (Equiv.Perm Δ)} (hP2 : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hP1 : P ≠ ⊥)
    (hF : 5 ≤ (fixSet Δ P).ncard) : Nat.card P = 2 ∧ (fixSet Δ P).ncard = 5 :=
  hA.card_eq_two_of_unitary hP2 hPN hP1 hF

theorem card_eq_two_of_subset_fixSet_of_unitary_four (hA : IsBenderAction ↥L Δ 2 3 e)
    {P : Subgroup (Equiv.Perm Δ)} (hP2 : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (L : Set (Equiv.Perm Δ))) (hP1 : P ≠ ⊥) {Λ : Set Δ}
    (hΛ : Λ ⊆ fixSet Δ P) (h5 : 5 ≤ Λ.ncard) : Nat.card P = 2 ∧ Λ.ncard = 5 := by
  have h := Set.ncard_le_ncard hΛ (Set.toFinite _)
  obtain ⟨h1, h2⟩ := hA.card_eq_two_of_unitary_four hP2 hPN hP1 (h5.trans h)
  exact ⟨h1, le_antisymm (h.trans h2.le) h5⟩

end IsBenderAction

theorem IsNaturalSE.isBenderAction_unitary_four (hL : IsNaturalSE L) {b : Δ}
    (h4 : Nat.card (rootCenter (seRadical L b)) = 4) (h5 : Nat.card Δ ≠ 5) :
    IsBenderAction ↥L Δ 2 3 5 := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hL
  have hn : n = 2 := by
    rw [hA.card_rootCenter_seRadical] at h4
    exact Nat.pow_right_injective le_rfl (h4.trans (by norm_num))
  subst hn
  rcases hA.benderType.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, a, -, ha⟩ | ⟨rfl, he, -⟩
  · exact absurd (by rw [hA.card_eq]; norm_num) h5
  · omega
  · have he' : e = 5 := by
      rw [he]
      norm_num
    rwa [he'] at hA

end Unitary

end CFSG.Holt.H78
