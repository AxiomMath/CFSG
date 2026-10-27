module

public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.BenderWC
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

@[expose] def eqE (T L : Subgroup G) : Set G :=
  {x | ∃ g : G, ∃ t ∈ T, t ∉ L ∧ x = g * t * g⁻¹}

omit [Finite G] in
theorem eqE_conj {L : Subgroup G} {x : G} (hx : x ∈ eqE T L) (c : G) :
    c * x * c⁻¹ ∈ eqE T L := by
  obtain ⟨g, t, htT, htL, rfl⟩ := hx
  exact ⟨c * g, t, htT, htL, by group⟩

theorem eqE_eq_isConj (hA : secA T T₁ = normIn T T₁) (hP : MaxPair T T₁) (hS : Sec3Global T)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀L : t₀ ∉ normIn T T₁) :
    eqE T (normIn T T₁) = {x | IsConj t₀ x} := by
  ext x
  constructor
  · rintro ⟨g, t, htT, htL, rfl⟩
    have h1 : t₀ ∉ secA T T₁ := by rwa [hA]
    have h2 : t ∉ secA T T₁ := by rwa [hA]
    obtain ⟨z, -, hz⟩ := secA_transitive hP hS ht₀ h1 htT h2
    refine isConj_iff.2 ⟨g * z, ?_⟩
    rw [← hz]
    group
  · intro hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    exact ⟨c, t₀, ht₀, ht₀L, hc.symm⟩

theorem normIn_eq_of_ne_bot (hA : secA T T₁ = normIn T T₁) (hP : MaxPair T T₁)
    (hS : Sec3Global T) {x : G} (hne : conjSubgroup x T ≠ T)
    (hL : normIn T (conjSubgroup x T) ≠ ⊥) : normIn T (conjSubgroup x T) = normIn T T₁ := by
  have c := Cfg.of_conj hP.wc hne hL
  obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.ne₁
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  obtain ⟨hfT', hfN⟩ := mem_normIn.1 hf
  have hfD : f ∈ normD T := by
    refine ⟨⟨x⁻¹, x⁻¹ * f * x, ?_, ?_, ?_⟩, hfN⟩
    · exact mem_conjSubgroup.1 hfT'
    · intro h1
      apply hf1'
      have : f = x * (x⁻¹ * f * x) * x⁻¹ := by group
      rw [this, h1]
      group
    · group
  have hLC : normIn T T₁ ≤ Subgroup.centralizer (normD T) := by
    rw [← hA]
    exact secA_le_centralizer_normD hP hS
  have hle : normIn T T₁ ≤ normIn T (conjSubgroup x T) := by
    intro y hy
    refine mem_normIn.2 ⟨normIn_le _ _ hy, ?_⟩
    have hyf : f * y = y * f := Subgroup.mem_centralizer_iff.1 (hLC hy) f hfD
    have hyc : y ∈ Subgroup.centralizer ({f} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hyf.symm
    exact (hP.wc.conj x).centralizer_le_normalizer hfT' hf1' hyc
  exact (Subgroup.eq_of_le_of_card_ge hle (hP.maximal x hne)).symm

theorem mem_left_of_mem_eqE_of_mem_normalizer (hA : secA T T₁ = normIn T T₁)
    (hP : MaxPair T T₁) (hS : Sec3Global T) {f : G} (hf : f ∈ eqE T (normIn T T₁))
    (hfN : f ∈ Subgroup.normalizer (T : Set G)) : f ∈ T := by
  obtain ⟨h, t, htT, htL, rfl⟩ := hf
  by_cases hh : conjSubgroup h⁻¹ T = T
  · have hh' : h⁻¹ ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hh
    have hh'' : h ∈ Subgroup.normalizer (T : Set G) := by
      simpa using (Subgroup.normalizer (T : Set G)).inv_mem hh'
    exact conj_mem_of_mem_normalizer hh'' htT
  · exfalso
    have hf1 : conjSubgroup t (conjSubgroup h⁻¹ T) = conjSubgroup h⁻¹ T := by
      have hfT : conjSubgroup (h * t * h⁻¹) T = T := mem_normalizer_iff_conjSubgroup_eq.1 hfN
      rw [conjSubgroup_conjSubgroup]
      have e : t * h⁻¹ = h⁻¹ * (h * t * h⁻¹) := by group
      rw [e, ← conjSubgroup_conjSubgroup, hfT]
    have htN : t ∈ Subgroup.normalizer ((conjSubgroup h⁻¹ T : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.2 hf1
    have ht1 : t ≠ 1 := fun h1 => htL (h1 ▸ (normIn T T₁).one_mem)
    have hne : normIn T (conjSubgroup h⁻¹ T) ≠ ⊥ :=
      Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨t, mem_normIn.2 ⟨htT, htN⟩⟩,
        fun h1 => ht1 (congrArg Subtype.val h1)⟩
    have hEq := normIn_eq_of_ne_bot hA hP hS hh hne
    have : t ∈ normIn T (conjSubgroup h⁻¹ T) := mem_normIn.2 ⟨htT, htN⟩
    rw [hEq] at this
    exact htL this

omit [Finite G] in
theorem dihedral_even_central_mem {S : Set G} {x y : G} (hx : x ∈ S) (hy : y ∈ S)
    (hxx : x * x = 1) (hyy : y * y = 1)
    (hS : ∀ g ∈ Subgroup.zpowers (x * y), ∀ s ∈ S, g⁻¹ * s * g ∈ S) {m : ℕ} (hm0 : 0 < m)
    (hm : orderOf (x * y) = 2 * m) :
    ∃ z : G, z * z = 1 ∧ z ≠ 1 ∧ x * z = z * x ∧ y * z = z * y ∧ x * z ∈ S ∧ y * z ∈ S := by
  have hzz : (x * y) ^ m * (x * y) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hm]
    exact pow_orderOf_eq_one _
  have hzinv : ((x * y) ^ m)⁻¹ = (x * y) ^ m := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ m = (x * y) ^ m * x := by
    have h1 : x * (x * y) ^ m * x⁻¹ = (x * y) ^ m := by
      rw [← conj_pow, left_invol_inverts hxx hyy, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxw : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have hyz : y * (x * y) ^ m = (x * y) ^ m * y := by
    calc y * (x * y) ^ m = x * (x * y) * (x * y) ^ m := by rw [hxw]
      _ = x * ((x * y) * (x * y) ^ m) := mul_assoc _ _ _
      _ = x * ((x * y) ^ m * (x * y)) := by rw [(Commute.self_pow (x * y) m).eq]
      _ = (x * (x * y) ^ m) * (x * y) := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * x) * (x * y) := by rw [hxz]
      _ = (x * y) ^ m * (x * (x * y)) := mul_assoc _ _ _
      _ = (x * y) ^ m * y := by rw [hxw]
  have hconj : ∀ (j : ℕ) (s : G), s ∈ S → ((x * y) ^ j)⁻¹ * s * (x * y) ^ j ∈ S :=
    fun j s hs => hS _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j) s hs
  refine ⟨(x * y) ^ m, hzz, pow_ne_one_of_lt_orderOf hm0.ne' (by omega), hxz, hyz, ?_⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hx' : x * (x * y) ^ m = ((x * y) ^ k)⁻¹ * x * (x * y) ^ k := by
      rw [inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hxx hyy) k,
        show 2 * k = m by omega, hzinv, hxz]
    have hy' : y * (x * y) ^ m = ((x * y) ^ k)⁻¹ * y * (x * y) ^ k := by
      rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hxx hyy) k,
        show 2 * k = m by omega, hzinv, hyz]
    exact ⟨hx' ▸ hconj k x hx, hy' ▸ hconj k y hy⟩
  · have hw : ((x * y) ^ (2 * k))⁻¹ = (x * y) ^ (m + 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show 2 * k + (m + 1) = orderOf (x * y) by omega]
      exact pow_orderOf_eq_one _
    have hx' : x * (x * y) ^ m = ((x * y) ^ k)⁻¹ * y * (x * y) ^ k := by
      rw [inv_pow_mul_mul_pow_of_inverts (right_invol_inverts hxx hyy) k, hw, pow_succ']
      have hxy : x * y * y = x := by rw [mul_assoc, hyy, mul_one]
      calc x * (x * y) ^ m = (x * y) * y * (x * y) ^ m := by rw [hxy]
        _ = (x * y) * (y * (x * y) ^ m) := mul_assoc _ _ _
        _ = (x * y) * ((x * y) ^ m * y) := by rw [hyz]
        _ = (x * y) * (x * y) ^ m * y := (mul_assoc _ _ _).symm
    have hy' : y * (x * y) ^ m = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := by
      have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hxx hyy) (k + 1)
      calc y * (x * y) ^ m = (x * y)⁻¹ * x * (x * y) ^ m := by rw [← invol_eq_inv_mul_mul hyy]
        _ = (x * y)⁻¹ * ((x * y) ^ m * x) := by rw [mul_assoc, hxz]
        _ = (x * y)⁻¹ * (x * y) ^ m * x := (mul_assoc _ _ _).symm
        _ = ((x * y) ^ m * (x * y))⁻¹ * x := by rw [mul_inv_rev ((x * y) ^ m) (x * y), hzinv]
        _ = ((x * y) ^ (2 * (k + 1)))⁻¹ * x := by
          rw [show 2 * (k + 1) = m + 1 by omega, pow_succ]
        _ = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := h1.symm
    exact ⟨hx' ▸ hconj k y hy, hy' ▸ hconj (k + 1) x hx⟩

omit [Finite G] in
theorem mul_self_eq_one_of_mem_eqE (hT : IsWC T) {e : G} (he : e ∈ eqE T (normIn T T₁)) :
    e * e = 1 := by
  obtain ⟨g, t, htT, -, rfl⟩ := he
  have htt : t * t = 1 := elemAbelian_mul_self hT.1 htT
  calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    _ = 1 := by rw [htt]; group

omit [Finite G] in
theorem ne_one_of_mem_eqE {e : G} (he : e ∈ eqE T (normIn T T₁)) : e ≠ 1 := by
  obtain ⟨g, t, htT, htL, rfl⟩ := he
  intro h
  apply htL
  have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
  rw [this, h]
  simp

theorem central_mem_of_mem_eqE (hA : secA T T₁ = normIn T T₁) (hP : MaxPair T T₁)
    (hS : Sec3Global T) {c t z : G} (htT : t ∈ T) (htL : t ∉ normIn T T₁)
    (hez : c * t * c⁻¹ * z = z * (c * t * c⁻¹))
    (hezE : c * t * c⁻¹ * z ∈ eqE T (normIn T T₁)) : c⁻¹ * z * c ∈ T := by
  have ht1 : t ≠ 1 := fun h => htL (h ▸ (normIn T T₁).one_mem)
  set z' := c⁻¹ * z * c with hz'
  have hcomm : t * z' = z' * t := by
    calc t * z' = c⁻¹ * (c * t * c⁻¹ * z) * c := by rw [hz']; group
      _ = c⁻¹ * (z * (c * t * c⁻¹)) * c := by rw [hez]
      _ = z' * t := by rw [hz']; group
  have hz'N : z' ∈ Subgroup.normalizer (T : Set G) :=
    hP.wc.centralizer_le_normalizer htT ht1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have htz : t * z' ∈ eqE T (normIn T T₁) := by
    have := eqE_conj hezE c⁻¹
    have e : c⁻¹ * (c * t * c⁻¹ * z) * c⁻¹⁻¹ = t * z' := by rw [hz']; group
    rwa [e] at this
  have htzN : t * z' ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer htT) hz'N
  have htzT := mem_left_of_mem_eqE_of_mem_normalizer hA hP hS htz htzN
  have := T.mul_mem (T.inv_mem htT) htzT
  simpa using this

theorem orderOf_mul_cases_eqE (hA : secA T T₁ = normIn T T₁) (hP : MaxPair T T₁)
    (hS : Sec3Global T) {e f : G} (he : e ∈ eqE T (normIn T T₁)) (hf : f ∈ eqE T (normIn T T₁)) :
    orderOf (e * f) ∣ 2 ∨ Odd (orderOf (e * f)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn2, hnodd⟩ := hcon
  obtain ⟨m, hm⟩ := Nat.not_odd_iff_even.1 hnodd
  have hm0 : 0 < m := by
    have := orderOf_pos (e * f)
    omega
  have hee := mul_self_eq_one_of_mem_eqE hP.wc he
  have hff := mul_self_eq_one_of_mem_eqE hP.wc hf
  obtain ⟨z, -, hz1, hez, hfz, hezE, hfzE⟩ := dihedral_even_central_mem he hf hee hff
    (fun g _ s hs => by simpa using eqE_conj hs g⁻¹) hm0 (by omega)
  obtain ⟨c, t, htT, htL, rfl⟩ := he
  obtain ⟨c', t', ht'T, ht'L, rfl⟩ := hf
  have hzc := central_mem_of_mem_eqE hA hP hS htT htL hez hezE
  have hzc' := central_mem_of_mem_eqE hA hP hS ht'T ht'L hfz hfzE
  have hzT : z ∈ conjSubgroup c T := by
    rw [mem_conjSubgroup]; exact hzc
  have hzT' : z ∈ conjSubgroup c' T := by
    rw [mem_conjSubgroup]; exact hzc'
  have hTeq : conjSubgroup c' T = conjSubgroup c T := by
    have h1 := (hP.wc.conj c).conj_eq_of_inf_ne_bot (g := c' * c⁻¹) (by
      intro hbot
      have hzm : z ∈ conjSubgroup c T ⊓ conjSubgroup (c' * c⁻¹) (conjSubgroup c T) := by
        refine ⟨hzT, ?_⟩
        rw [conjSubgroup_conjSubgroup, show c' * c⁻¹ * c = c' by group]
        exact hzT'
      rw [hbot, Subgroup.mem_bot] at hzm
      exact hz1 hzm)
    rwa [conjSubgroup_conjSubgroup, show c' * c⁻¹ * c = c' by group] at h1
  have hel : c * t * c⁻¹ ∈ conjSubgroup c T := by
    rw [mem_conjSubgroup]
    have e : c⁻¹ * (c * t * c⁻¹) * c = t := by group
    rw [e]; exact htT
  have hfl : c' * t' * c'⁻¹ ∈ conjSubgroup c T := by
    rw [← hTeq, mem_conjSubgroup]
    have e : c'⁻¹ * (c' * t' * c'⁻¹) * c' = t' := by group
    rw [e]; exact ht'T
  have habel := isElemAbelian_conjSubgroup hP.wc.1 c
  have hprod : (c * t * c⁻¹) * (c' * t' * c'⁻¹) ∈ conjSubgroup c T :=
    (conjSubgroup c T).mul_mem hel hfl
  have hsq : ((c * t * c⁻¹) * (c' * t' * c'⁻¹)) ^ 2 = 1 := habel.2 _ hprod
  exact hn2 (orderOf_dvd_of_pow_eq_one hsq)

section Wreath

open SemidirectProduct

theorem not_isSimpleGroup_wreath {P : Type*} [Group P] [Nontrivial P] {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSimpleGroup ((Fin n → P) ⋊[CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin n) P]
      Equiv.Perm (Fin n)) := by
  intro hsimple
  set B : Subgroup ((Fin n → P) ⋊[CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin n) P]
      Equiv.Perm (Fin n)) := rightHom.ker with hB
  have hBn : B.Normal := MonoidHom.normal_ker _
  have : B.Normal := hBn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
  · obtain ⟨p, hp⟩ := exists_ne (1 : P)
    set j : Fin n := ⟨0, by omega⟩ with hj
    set b : Fin n → P := Pi.mulSingle j p with hb
    have hmem : (inl b :
        (Fin n → P) ⋊[CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin n) P] Equiv.Perm (Fin n)) ∈ B := by
      rw [hB, MonoidHom.mem_ker]
      exact rightHom_inl _
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : b = 1 := inl_injective (hmem.trans (map_one inl).symm)
    have h2 := congrFun h1 j
    rw [hb] at h2
    simp at h2
    exact hp h2
  · obtain ⟨x, hx⟩ := rightHom_surjective (G := Equiv.Perm (Fin n))
      (N := Fin n → P) (φ := CFSG.Timmesfeld.Bridge.Asc72.permAct (Fin n) P)
      (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
    have hxB : x ∈ B := by rw [h]; exact Subgroup.mem_top x
    rw [hB, MonoidHom.mem_ker] at hxB
    rw [hxB] at hx
    have h3 : (1 : Equiv.Perm (Fin n)) = Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ := hx
    have h4 := congrArg (fun σ => σ ⟨0, by omega⟩) h3
    simp at h4

end Wreath

theorem secA_ne_normIn (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hP : MaxPair T T₁)
    (hS : Sec3Global T) : secA T T₁ ≠ normIn T T₁ := by
  intro hA
  have hs₁ := hP.sec3_conj hS (Subgroup.one_mem (Subgroup.normalizer (T : Set G)))
  rw [conjSubgroup_one] at hs₁
  obtain ⟨t₀, ht₀T, ht₀M⟩ := IsConcreteLE.not_le_iff_exists.1 hs₁.not_le_cfgM
  have ht₀L : t₀ ∉ normIn T T₁ := fun h => ht₀M (Cfg.normIn_le_cfgM_left T T₁ h)
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀L (h ▸ (normIn T T₁).one_mem)
  have hE := eqE_eq_isConj hA hP hS ht₀T ht₀L
  have ht₀E : t₀ ∈ eqE T (normIn T T₁) := ⟨1, t₀, ht₀T, ht₀L, by simp⟩
  have hord : ∀ d ∈ eqE T (normIn T T₁), orderOf d = 2 := fun d hd =>
    orderOf_eq_prime (by simpa [pow_two] using mul_self_eq_one_of_mem_eqE hP.wc hd)
      (ne_one_of_mem_eqE hd)
  have hclos : Subgroup.closure (eqE T (normIn T T₁)) = ⊤ := by
    have hnc : Subgroup.normalClosure (eqE T (normIn T T₁)) =
        Subgroup.closure (eqE T (normIn T T₁)) := by
      refine le_antisymm (Subgroup.closure_mono fun x hx => ?_)
        (Subgroup.closure_le _ |>.2 Subgroup.subset_normalClosure)
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      obtain ⟨c, hc⟩ := isConj_iff.1 hax
      rw [← hc]
      exact eqE_conj ha c
    have hPn : (Subgroup.closure (eqE T (normIn T T₁))).Normal :=
      hnc ▸ Subgroup.normalClosure_normal
    have := hPn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.closure (eqE T (normIn T T₁))) with h | h
    · exfalso
      have : t₀ ∈ Subgroup.closure (eqE T (normIn T T₁)) := Subgroup.subset_closure ht₀E
      rw [h, Subgroup.mem_bot] at this
      exact ht₀1 this
    · exact h
  have hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥ := by
    intro N hN hsolv
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      subst h
      have : Group.IsSolvable G :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.topEquiv.symm.toMonoidHom)
          (MulEquiv.injective _)
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 this a b)
  have hTtop : T ≠ ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (elemAbelian_mul_comm hP.wc.1 (h ▸ Subgroup.mem_top a) (h ▸ Subgroup.mem_top b))
  have hcl : ∀ u ∈ eqE T (normIn T T₁), u ∈ T → ∀ v ∈ eqE T (normIn T T₁), Commute u v → v ∈ T := by
    intro u hu huT v hv hc
    have hvN : v ∈ Subgroup.normalizer (T : Set G) :=
      hP.wc.centralizer_le_normalizer huT (ne_one_of_mem_eqE hu)
        (Subgroup.mem_centralizer_singleton_iff.2 hc.eq.symm)
    exact mem_left_of_mem_eqE_of_mem_normalizer hA hP hS hv hvN
  have hTbot : T ≠ ⊥ := fun h => hP.nontriv (le_bot_iff.1 ((normIn_le T T₁).trans h.le))
  rcases hTO G (eqE T (normIn T T₁)) ⟨t₀, hE⟩ hord
    (fun d hd e he => orderOf_mul_cases_eqE hA hP hS hd he) hclos hrad
    ⟨T, hTtop, ⟨t₀, ht₀E, ht₀T⟩, hcl⟩ with hB | ⟨f, n, -, hn, ⟨e⟩⟩ | hAlm
  · obtain ⟨x₀, hx₀⟩ := hP.conj
    have hne : conjSubgroup x₀ T ≠ T := hx₀ ▸ hP.ne
    have := hBW G hB T hP.wc hTbot x₀ hne
    exact hP.nontriv (hx₀ ▸ this)
  · have hsW := e.symm.isSimpleGroup
    exact not_isSimpleGroup_wreath (by omega) hsW
  · obtain ⟨M, hMn, hMmin, -, -, -, h2, -, -⟩ := hAlm
    have := hMn
    have hM := (IsSimpleGroup.eq_bot_or_eq_top_of_normal M).resolve_left hMmin.2.1
    rw [hM, Subgroup.index_top] at h2
    omega

end CFSG.CGT.Timmesfeld75
