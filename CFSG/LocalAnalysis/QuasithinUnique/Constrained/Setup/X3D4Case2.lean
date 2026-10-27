module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3LinesSix
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Setup

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X5

theorem simple_on_subtype {X : Type*} [Group X] {V' : Type*} [AddCommGroup V']
    [Module (ZMod 2) V'] {σ : X →* (V' ≃ₗ[ZMod 2] V')} {L : Subgroup X}
    {U : Submodule (ZMod 2) V'} (hU : IsLSimple σ L U)
    (hinv : ∀ n, ∀ u ∈ U, σ n u ∈ U) :
    ∀ W' : Submodule (ZMod 2) ↥U, Offender.IsInvariant (resHom σ U hinv) L W' →
      W' = ⊥ ∨ W' = ⊤ := by
  intro W' hW'
  have hW''inv : Offender.IsInvariant σ L (W'.map U.subtype) := by
    rintro l hl _ ⟨u, hu, rfl⟩
    exact ⟨resHom σ U hinv l u, hW' l hl u hu, rfl⟩
  have hW''le : W'.map U.subtype ≤ U := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  rcases hU.2.2 _ hW''inv hW''le with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have h1 : (u : V') ∈ W'.map U.subtype := ⟨u, hu, rfl⟩
    rw [h] at h1
    have h2 := (Submodule.mem_bot _).1 h1
    exact (Submodule.mem_bot _).2 (Subtype.ext h2)
  · right
    rw [eq_top_iff]
    intro u _
    have h1 : (u : V') ∈ W'.map U.subtype := by rw [h]; exact u.2
    obtain ⟨w, hw, hwu⟩ := h1
    have h2 : w = u := Subtype.ext hwu
    rw [← h2]
    exact hw

section Center

variable {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal]

omit [L.Normal] in
theorem card_center_one_or_three (hL : CFSG.IsQuasisimple ↥L)
    (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3 := by
  have hperf : Group.IsPerfect ↥L := hL.1
  let π : ↥L →* alternatingGroup (Fin 6) :=
    eQ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ eQ.injective, QuotientGroup.eq_one_iff]
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨q, rfl⟩ := eQ.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have := CFSG.SectionRank.alternating_small_odd_cover_bound (n := 6) (by norm_num) (by norm_num)
    π hπ (by rw [hker]) (by rw [hker]; exact hodd)
  rw [hker] at this
  exact this.2 (Or.inl rfl)

omit [L.Normal] in
theorem exists_generator (h3 : Nat.card (Subgroup.center ↥L) = 3) :
    ∃ c : H, (Subgroup.center ↥L).map L.subtype = Subgroup.zpowers c ∧ c ≠ 1 ∧ c ^ 3 = 1 := by
  have hZne : (Subgroup.center ↥L) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h3
    omega
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
  set c : H := (z.1 : H) with hc
  have hc1 : c ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hcmem : c ∈ (Subgroup.center ↥L).map L.subtype := ⟨z.1, z.2, rfl⟩
  have hcard : Nat.card ((Subgroup.center ↥L).map L.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, h3]
  have hord : orderOf c ∣ 3 := by
    have h1 : orderOf (⟨c, hcmem⟩ : ↥((Subgroup.center ↥L).map L.subtype)) ∣
        Nat.card ↥((Subgroup.center ↥L).map L.subtype) := orderOf_dvd_natCard _
    rw [hcard, Subgroup.orderOf_mk] at h1
    exact h1
  have hord3 : orderOf c = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h1 | h3'
    · exact absurd (orderOf_eq_one_iff.1 h1) hc1
    · exact h3'
  have hz3 : Subgroup.zpowers c ≤ (Subgroup.center ↥L).map L.subtype :=
    (Subgroup.zpowers_le).2 hcmem
  refine ⟨c, (Subgroup.eq_of_le_of_card_ge hz3 ?_).symm, hc1, ?_⟩
  · rw [hcard, Nat.card_zpowers, hord3]
  · rw [← hord3]; exact pow_orderOf_eq_one c

end Center

section Summand

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {H : Type} [Group H] [Finite H]
  (ρ : H →* (W ≃ₗ[ZMod 2] W)) (L A : Subgroup H) [L.Normal]

omit [Finite W] [L.Normal] in
theorem faithful_on_summand (hL : CFSG.IsQuasisimple ↥L) (h3 : Nat.card (Subgroup.center ↥L) = 3)
    {c : H} (hZc : (Subgroup.center ↥L).map L.subtype = Subgroup.zpowers c)
    {σ : H →* ((W ⧸ fixSub ρ L) ≃ₗ[ZMod 2] (W ⧸ fixSub ρ L))}
    {U : Submodule (ZMod 2) (W ⧸ fixSub ρ L)}
    (hUinv : Offender.IsInvariant σ L U) (hcnt : ∃ u ∈ U, σ c u ≠ u) :
    (resSub σ L U hUinv).ker = ⊥ := by
  have hcmem : c ∈ (Subgroup.center ↥L).map L.subtype := by
    rw [hZc]; exact Subgroup.mem_zpowers c
  obtain ⟨zc, hzc, hzcc⟩ := hcmem
  have hcL : c ∈ L := by rw [← hzcc]; exact zc.2
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL (MonoidHom.normal_ker (resSub σ L U hUinv))
    with htop | hle
  · exfalso
    obtain ⟨u, hu, hne⟩ := hcnt
    apply hne
    have : zc ∈ (resSub σ L U hUinv).ker := by rw [htop]; trivial
    have h1 : resSub σ L U hUinv zc = 1 := MonoidHom.mem_ker.1 this
    have h2 := congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => (f ⟨u, hu⟩ : ↥U).1) h1
    have h3 : σ (zc : H) u = u := by simpa [resSub_apply] using h2
    have hzc' : (zc : H) = c := hzcc
    rwa [hzc'] at h3
  · have hdvd : Nat.card (resSub σ L U hUinv).ker ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.card_dvd_of_le hle
    rw [h3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : (resSub σ L U hUinv).ker = Subgroup.center ↥L :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h3, h3'])
      obtain ⟨u, hu, hne⟩ := hcnt
      apply hne
      have : zc ∈ (resSub σ L U hUinv).ker := by rw [heq]; exact hzc
      have h1 : resSub σ L U hUinv zc = 1 := MonoidHom.mem_ker.1 this
      have h2 := congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => (f ⟨u, hu⟩ : ↥U).1) h1
      have h3'' : σ (zc : H) u = u := by simpa [resSub_apply] using h2
      have hzc' : (zc : H) = c := hzcc
      rwa [hzc'] at h3''

theorem six_point_case_two (hL : CFSG.IsQuasisimple ↥L)
    (eQ : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hcent : Subgroup.centralizer (L : Set H) = (Subgroup.center ↥L).map L.subtype)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (sec : D4Section ρ L A)
    (hcard : Nat.card ↥sec.M ≤ 64)
    (hN : ∃ z ∈ Subgroup.center ↥L, ∃ m ∈ sec.M, cvAct ρ L (z : H) m ≠ m) :
    ∃ θ : H →* Equiv.Perm (Fin 6), θ.ker = (Subgroup.center ↥L).map L.subtype ∧
      L.map θ = alternatingGroup (Fin 6) := by
  classical
  have hperf : Group.IsPerfect ↥L := hL.1
  set σ := cvAct ρ L with hσ
  obtain ⟨z₀, hz₀, m₀, hm₀, hne⟩ := hN
  have h3 : Nat.card (Subgroup.center ↥L) = 3 := by
    rcases card_center_one_or_three L hL eQ hodd with h1 | h3
    · exfalso
      have hsub : Subsingleton (Subgroup.center ↥L) := (Nat.card_eq_one_iff_unique.1 h1).1
      have : z₀ = 1 := by
        have := hsub.elim (⟨z₀, hz₀⟩ : Subgroup.center ↥L) 1
        exact congrArg Subtype.val this
      apply hne
      rw [this]
      simp
    · exact h3
  obtain ⟨c, hZc, hc1, hc3⟩ := exists_generator L h3
  have hcmem : c ∈ (Subgroup.center ↥L).map L.subtype := by
    rw [hZc]; exact Subgroup.mem_zpowers c
  obtain ⟨zc, hzc, hzcc⟩ := hcmem
  have hcL : c ∈ L := by rw [← hzcc]; exact zc.2
  have hcZ : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    have : (⟨c, hcL⟩ : ↥L) = zc := Subtype.ext hzcc.symm
    rw [this]; exact hzc
  have hcM : ∃ m ∈ sec.M, σ c m ≠ m := by
    by_contra hcon
    push Not at hcon
    have hcmem' : c ∈ centSub σ sec.M := fun u hu => hcon u hu
    have hz₀mem : (z₀ : H) ∈ (Subgroup.center ↥L).map L.subtype := ⟨z₀, hz₀, rfl⟩
    rw [hZc] at hz₀mem
    have : (z₀ : H) ∈ centSub σ sec.M := (Subgroup.zpowers_le.2 hcmem') hz₀mem
    exact hne (this m₀ hm₀)
  obtain ⟨U₁, hU₁s, hU₁c⟩ : ∃ U ∈ sec.s, ∃ u ∈ U, σ c u ≠ u := by
    by_contra hall
    push Not at hall
    obtain ⟨m, hm, hne'⟩ := hcM
    have hle : sec.s.sup id ≤ LinearMap.ker
        ((σ c : (W ⧸ fixSub ρ L) →ₗ[ZMod 2] (W ⧸ fixSub ρ L)) - LinearMap.id) := by
      refine Finset.sup_le fun U hU u hu => ?_
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.sub_apply]
      show σ c u - u = 0
      rw [hall U hU u hu, sub_self]
    rw [sec.ssup] at hle
    have h0 := LinearMap.mem_ker.1 (hle hm)
    rw [LinearMap.sub_apply] at h0
    exact hne' (sub_eq_zero.1 h0)
  have hsU := sec.ssimple U₁ hU₁s
  have hUinv : Offender.IsInvariant σ L U₁ := hsU.1.1
  have hUM : U₁ ≤ sec.M := by
    rw [← sec.ssup]; exact Finset.le_sup (f := id) hU₁s
  have hcomm : ∀ l ∈ L, ∀ x, σ c (σ l x) = σ l (σ c x) := by
    intro l hl x
    have := Subgroup.mem_center_iff.1 hcZ ⟨l, hl⟩
    have h2 : l * c = c * l := congrArg Subtype.val this
    rw [← LinearEquiv.mul_apply, ← map_mul, ← h2, map_mul, LinearEquiv.mul_apply]
  have hfix : ∀ u ∈ U₁, σ c u = u → u = 0 := by
    intro u hu hfu
    let K : Submodule (ZMod 2) (W ⧸ fixSub ρ L) := U₁ ⊓ LinearMap.ker
      ((σ c : (W ⧸ fixSub ρ L) →ₗ[ZMod 2] (W ⧸ fixSub ρ L)) - LinearMap.id)
    have hK : Offender.IsInvariant σ L K := by
      intro l hl x hx
      refine ⟨hUinv l hl x hx.1, LinearMap.mem_ker.2 ?_⟩
      have h0 : (((σ c : (W ⧸ fixSub ρ L) →ₗ[ZMod 2] (W ⧸ fixSub ρ L)) - LinearMap.id :
          (W ⧸ fixSub ρ L) →ₗ[ZMod 2] (W ⧸ fixSub ρ L)) x) = 0 := LinearMap.mem_ker.1 hx.2
      rw [LinearMap.sub_apply] at h0 ⊢
      have h1 : σ c x = x := sub_eq_zero.1 h0
      show σ c (σ l x) - σ l x = 0
      rw [hcomm l hl, h1, sub_self]
    rcases hsU.1.2.2 K hK inf_le_left with hb | hfull
    · have hmem : u ∈ K := ⟨hu, LinearMap.mem_ker.2 (by
        rw [LinearMap.sub_apply]; show σ c u - u = 0; rw [hfu, sub_self])⟩
      rw [hb] at hmem
      exact (Submodule.mem_bot _).1 hmem
    · exfalso
      obtain ⟨u', hu', hne'⟩ := hU₁c
      have hmem : u' ∈ K := by rw [hfull]; exact hu'
      have h0 : (((σ c : (W ⧸ fixSub ρ L) →ₗ[ZMod 2] (W ⧸ fixSub ρ L)) - LinearMap.id :
          (W ⧸ fixSub ρ L) →ₗ[ZMod 2] (W ⧸ fixSub ρ L)) u') = 0 := LinearMap.mem_ker.1 hmem.2
      rw [LinearMap.sub_apply] at h0
      exact hne' (sub_eq_zero.1 h0)
  have hσc3 : ∀ x, σ c (σ c (σ c x)) = x := by
    intro x
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
    have : c * c * c = 1 := by
      calc c * c * c = c ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
        _ = 1 := hc3
    rw [this, map_one]
    rfl
  let T₁ : ↥U₁ ≃ₗ[ZMod 2] ↥U₁ := resSub σ L U₁ hUinv ⟨c, hcL⟩
  have hT₁val : ∀ u : ↥U₁, ((T₁ u : ↥U₁) : W ⧸ fixSub ρ L) = σ c u := fun u => rfl
  have hT₁ : OrderThree T₁ := by
    refine ⟨fun u => ?_, fun u hu => ?_⟩
    · refine Subtype.ext ?_
      rw [hT₁val, hT₁val]
      show σ c (σ c u) = u + σ c u
      have hv : σ c (σ c u) + σ c u + u ∈ U₁ := by
        refine U₁.add_mem (U₁.add_mem ?_ ?_) u.2
        · exact hUinv c hcL _ (hUinv c hcL _ u.2)
        · exact hUinv c hcL _ u.2
      have hvfix : σ c (σ c (σ c u) + σ c u + u : W ⧸ fixSub ρ L) = σ c (σ c u) + σ c u + u := by
        rw [map_add, map_add, hσc3]
        abel
      have hv0 := hfix _ hv hvfix
      have h2 : (σ c u + u) + (σ c u + u) = 0 := add_self_eq_zero_of_charTwo' (k := ZMod 2) _
      calc σ c (σ c u) = σ c (σ c u) + σ c u + u - (σ c u + u) := by abel
        _ = 0 - (σ c u + u) := by rw [hv0]
        _ = u + σ c u := by
          rw [zero_sub]
          exact (neg_eq_of_add_eq_zero_left h2).trans (add_comm _ _)
    · exact Subtype.ext (hfix u.1 u.2 (by rw [← hT₁val, hu]))
  have hlines := card_lines hT₁
  have hU1ne : U₁ ≠ ⊥ := hsU.1.2.1
  have hU1gt : 1 < Nat.card ↥U₁ := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact (Submodule.nontrivial_iff_ne_bot).2 hU1ne
  have hU1le : Nat.card ↥U₁ ≤ 64 :=
    (Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hUM)).trans hcard
  have hU1pow : Nat.card ↥U₁ = 2 ^ Module.finrank (ZMod 2) ↥U₁ := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U₁)
    rwa [Nat.card_zmod] at this
  have hker : (resSub σ L U₁ hUinv).ker = ⊥ := faithful_on_summand ρ L hL h3 hZc hUinv hU₁c
  have hinj : Function.Injective (resSub σ L U₁ hUinv) := (MonoidHom.ker_eq_bot_iff _).1 hker
  have hLcard : Nat.card ↥L = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [h3, Nat.card_congr eQ.toEquiv, card_alt6] at h1
    omega
  have hGLtoPerm : Function.Injective (fun g : ↥U₁ ≃ₗ[ZMod 2] ↥U₁ => g.toEquiv) :=
    fun g h hgh => LinearEquiv.ext fun x => congrArg (fun e : Equiv.Perm ↥U₁ => e x) hgh
  have hGLfin : Finite (↥U₁ ≃ₗ[ZMod 2] ↥U₁) := Finite.of_injective _ hGLtoPerm
  have hLle : Nat.card ↥L ≤ Nat.card (↥U₁ ≃ₗ[ZMod 2] ↥U₁) :=
    Nat.card_le_card_of_injective _ hinj
  have hLdvd : Nat.card ↥L ∣ Nat.card (↥U₁ ≃ₗ[ZMod 2] ↥U₁) := by
    have h1 := Subgroup.card_subgroup_dvd_card (resSub σ L U₁ hUinv).range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h1
  have hd6 : Module.finrank (ZMod 2) ↥U₁ ≤ 6 := by
    by_contra hd
    have h7 : 2 ^ 7 ≤ 2 ^ Module.finrank (ZMod 2) ↥U₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hU64 : Nat.card ↥U₁ = 64 := by
    generalize hd : Module.finrank (ZMod 2) ↥U₁ = d at hU1pow hd6
    interval_cases d <;> try omega
    ·
      exfalso
      have h1 : Nat.card (↥U₁ ≃ₗ[ZMod 2] ↥U₁) ≤ Nat.card (Equiv.Perm ↥U₁) :=
        Nat.card_le_card_of_injective _ hGLtoPerm
      rw [Nat.card_perm] at h1
      have h2 : Nat.card ↥U₁ = 4 := by omega
      rw [h2] at h1
      have h24 : Nat.factorial 4 = 24 := by decide
      rw [h24] at h1
      omega
    ·
      exfalso
      have hV : Module.finrank (ZMod 2) ↥U₁ = 4 := hd
      have h1 : Nat.card (↥U₁ ≃ₗ[ZMod 2] ↥U₁) = 20160 := by
        rw [Nat.card_congr (linearEquivGLFour hV).toEquiv]
        exact CFSG.GH74.Exceptional.card_GL_four_two
      rw [h1, hLcard] at hLdvd
      omega
  have hMeq : U₁ = sec.M :=
    CFSG.QuasithinUnique.Setup.Offender.submodule_eq_of_le_of_card_ge hUM (by rw [hU64]; exact hcard)
  have hUinvH : ∀ n, ∀ u ∈ U₁, σ n u ∈ U₁ := by
    intro n u hu
    rw [hMeq] at hu ⊢
    exact sec.Minv n u hu
  have hsimple := simple_on_subtype hsU.1 hUinvH
  exact six_point_of_lines (resHom σ U₁ hUinvH) L hL eQ hcent hZc hT₁ hU64 hsimple

end Summand

end CFSG.QuasithinUnique.Setup.X3
