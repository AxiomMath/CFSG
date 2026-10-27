module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbTorus

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_torus_of_map_eq_cz {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (O : Subgroup Q) [O.Normal] (hO : p.Coprime (Nat.card O)) {A B : Subgroup Q} {z : Q}
    (hA : IsPGroup p (A ⊔ Subgroup.zpowers z : Subgroup Q)) (hOB : O ≤ B) {F : Type*} [Field F]
    (ψ : Multiplicative F →* Q ⧸ O) (hψ : Function.Injective ψ)
    (hψA : ψ.range = A.map (QuotientGroup.mk' O))
    (hc : ∀ μ : Fˣ, ∃ c ∈ B.map (QuotientGroup.mk' O),
      c * QuotientGroup.mk' O z = QuotientGroup.mk' O z * c ∧ ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a))) :
    ∃ φ : Multiplicative F ≃* A, ∀ μ : Fˣ, ∃ t ∈ B, t * z = z * t ∧ ∀ a : Multiplicative F,
      t * (φ a : Q) * t⁻¹ = φ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a)) := by
  set A' : Subgroup Q := A ⊔ Subgroup.zpowers z with hA'
  have hAA' : A ≤ A' := le_sup_left
  have hzA' : z ∈ A' := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hinj' : ∀ x ∈ A', ∀ y ∈ A', QuotientGroup.mk' O x = QuotientGroup.mk' O y → x = y := by
    intro x hx y hy hxy
    have hmem : x * y⁻¹ ∈ A' ⊓ O := by
      refine ⟨A'.mul_mem hx (A'.inv_mem hy), ?_⟩
      have h1 : QuotientGroup.mk' O (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [inf_eq_bot_of_isPGroup hp hA hO, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  let g : A →* Q ⧸ O := (QuotientGroup.mk' O).comp A.subtype
  have hg : ∀ x : A, g x = QuotientGroup.mk' O (x : Q) := fun x => rfl
  have hginj : Function.Injective g := fun x y hxy =>
    Subtype.ext (hinj' _ (hAA' x.2) _ (hAA' y.2) hxy)
  have hgr : ψ.range = g.range := by
    rw [hψA, MonoidHom.range_comp, Subgroup.range_subtype]
  let φ : Multiplicative F ≃* A := (MonoidHom.ofInjective hψ).trans
    ((MulEquiv.subgroupCongr hgr).trans (MonoidHom.ofInjective hginj).symm)
  have hφ : ∀ a, g (φ a) = ψ a := by
    intro a
    change g ((MonoidHom.ofInjective hginj).symm
      (MulEquiv.subgroupCongr hgr (MonoidHom.ofInjective hψ a))) = ψ a
    rw [MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
  refine ⟨φ, fun μ => ?_⟩
  obtain ⟨_, ⟨b, hb, rfl⟩, hbz, hcψ⟩ := hc μ
  have hbA : QuotientGroup.mk' O b ∈
      Subgroup.normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) :=
    hψA ▸ mem_normalizer_range_of_torus ψ μ.ne_zero hcψ
  have hbZ : QuotientGroup.mk' O b ∈ Subgroup.normalizer
      ((Subgroup.zpowers (QuotientGroup.mk' O z) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) := by
    have hcen : QuotientGroup.mk' O b ∈
        Subgroup.centralizer (Subgroup.zpowers (QuotientGroup.mk' O z) : Set (Q ⧸ O)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      exact (Commute.zpow_left (Commute.symm hbz) k).eq
    exact Subgroup.centralizer_le_normalizer _ hcen
  have hbN : QuotientGroup.mk' O b ∈
      Subgroup.normalizer ((A'.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) := by
    rw [hA', Subgroup.map_sup, MonoidHom.map_zpowers]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hbA, hbZ⟩
  obtain ⟨o, ho, t, ht, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (comap_normalizer_map_le_sup hp O hO hA hbN)
  have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hot : QuotientGroup.mk' O (o * t) = QuotientGroup.mk' O t := by
    rw [map_mul, ho1, one_mul]
  refine ⟨t, by simpa using B.mul_mem (B.inv_mem (hOB ho)) hb, ?_, fun a => ?_⟩
  ·
    have hmem : t * z * t⁻¹ ∈ A' := (Subgroup.mem_normalizer_iff.mp ht _).mp hzA'
    have heq : t * z * t⁻¹ = z := by
      refine hinj' _ hmem _ hzA' ?_
      rw [map_mul, map_mul, map_inv, ← hot, hbz, mul_inv_cancel_right]
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [heq]
  · have hmem : t * (φ a : Q) * t⁻¹ ∈ A' :=
      (Subgroup.mem_normalizer_iff.mp ht _).mp (hAA' (φ a).2)
    refine hinj' _ hmem _ (hAA' (φ _).2) ?_
    rw [← hg, hφ, ← hcψ, ← hφ a, hg, map_mul, map_mul, map_inv, hot]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.isElemAbelian_d1LiftX_linTwo [Fact p.Prime] (h3 : D1PhaseThree p P M H R)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsSmallLinTwo p K) :
    IsElemAbelian p (d1LiftX p H R K) ∧ Nat.card (d1LiftX p H R K) = p ^ 2 := by
  obtain ⟨φ, -⟩ := hd.exists_torus_linTwo h3 hL
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a', rfl⟩ := φ.surjective a
    obtain ⟨b', rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hap : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have : (⟨x, hx⟩ : d1LiftX p H R K) ^ p = 1 := by rw [← ha, ← map_pow, hap, map_one]
    simpa using congrArg Subtype.val this
  · rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p 2 (by norm_num)]

theorem D1OneSmallData.exists_torus_linTwo_cz [Fact p.Prime] (h3 : D1PhaseThree p P M H R)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsSmallLinTwo p K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    ∃ φ : Multiplicative (GaloisField p 2) ≃* d1LiftX p H R K,
      ∀ μ : (GaloisField p 2)ˣ, ∃ t ∈ H ⊓ M, t * z = z * t ∧
        ∀ a : Multiplicative (GaloisField p 2), t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a)) := by
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨hzR, -, hzH, hzc⟩ := hz
  obtain ⟨T, hT, -⟩ := hd.exists_sylow
  obtain ⟨d, hdL, ⟨e₁⟩⟩ := hL
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdL
  set f : K ≃* PSL2GF p 2 := e₁.trans e₂
  have hfs : Function.Surjective (f : K →* PSL2GF p 2) := f.surjective
  set U : Sylow p (PSL2GF p 2) := T.mapSurjective hfs
  have hUT : (U : Subgroup (PSL2GF p 2)) = (T : Subgroup K).map (f : K →* PSL2GF p 2) :=
    Sylow.coe_mapSurjective hfs T
  have hTcard : Nat.card (T : Subgroup K) = p ^ 2 := by
    rw [← (psl2GF_sylow p 2 (by norm_num) U).2, hUT, Subgroup.card_map_of_injective
      (show Function.Injective (f : K →* PSL2GF p 2) from f.injective)]
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup _) = p ^ 2 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  obtain ⟨ψ, hψinj, hψrange, hc⟩ := exists_torus_param_of_mulEquiv_psl2GF hp2 (by norm_num) f
    ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) inf_le_right hcard
  obtain ⟨z', hzR', hzK', hzp', hzc'⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR' hzK' hzp' hzc'
  have hT1 : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ≠ ⊥ :=
    fun h => hd.noncyclic (by rw [h]; infer_instance)
  set O := primeComplementCore (G := H) p with hOdef
  set X := d1LiftX p H R K with hXdef
  have hXH : X ≤ H := d1LiftX_le_H p H R K
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hcY : ∀ μ : (GaloisField p 2)ˣ,
      ∃ c ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O),
        c * QuotientGroup.mk' O zH = QuotientGroup.mk' O zH * c ∧
        ∀ a : Multiplicative (GaloisField p 2),
          c * ψ a * c⁻¹ =
            ψ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcK, hcψ⟩ := hc μ
    have hcN : c ∈ K ⊓ Subgroup.normalizer
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) :=
      ⟨hcK, by rw [← hψrange]; exact mem_normalizer_range_of_torus ψ μ.ne_zero hcψ⟩
    exact ⟨c, hN _ le_rfl hT1 hcN, Subgroup.mem_centralizer_iff.mp hzc c hcK, hcψ⟩
  have hXz : IsPGroup p ((X.subgroupOf H) ⊔ Subgroup.zpowers zH : Subgroup H) := by
    have hle : (X.subgroupOf H) ⊔ Subgroup.zpowers zH ≤ R.subgroupOf H := by
      refine sup_le (Subgroup.subgroupOf_mono H (d1LiftX_le p H R K)) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_subgroupOf.mpr hzR
    exact (hd.cfg.ext.isPGroup.comap_subtype (K := H)).to_le hle
  have hNB : O ≤ (H ⊓ M).subgroupOf H := fun o ho =>
    Subgroup.mem_subgroupOf.mpr
      (le_inf (glbPrimeCore_le p H) h3.primeCore_le
        ((mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)))
  have hψX : ψ.range = (X.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [hψrange, hd.cfg.map_d1LiftX_eq_inf]
  obtain ⟨φ, hφ⟩ := exists_torus_of_map_eq_cz Fact.out O (primeComplementCore_coprime p) hXz hNB
    ψ hψinj hψX hcY
  refine ⟨φ.trans (Subgroup.subgroupOfEquivOfLe hXH), fun μ => ?_⟩
  obtain ⟨t, ht, htz, htφ⟩ := hφ μ
  refine ⟨t, Subgroup.mem_subgroupOf.mp ht, congrArg Subtype.val htz, fun a => ?_⟩
  exact congrArg Subtype.val (htφ a)

theorem D1OneSmallData.exists_irr_linTwo_period_cz [Fact p.Prime] (h3 : D1PhaseThree p P M H R)
    (hd : D1OneSmallData p P M H R Rbar K) (hL : IsSmallLinTwo p K) (hp5 : 5 ≤ p) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    ∃ t : G, t ∈ H ⊓ M ∧ t * z = z * t ∧
      t ∈ Subgroup.normalizer ((d1LiftX p H R K : Subgroup G) : Set G) ∧
      (∀ k : ℕ, ¬ (p + 1) / 2 ∣ k → ∀ Y : Subgroup G, Y ≤ d1LiftX p H R K →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = d1LiftX p H R K) ∧
      ∃ l : ℕ, 1 ≤ l ∧ Nat.Coprime (l - 1) p ∧ ∀ x ∈ d1LiftX p H R K,
        t ^ ((p + 1) / 2) * x * (t ^ ((p + 1) / 2))⁻¹ = x ^ l := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨φ, htor⟩ := hd.exists_torus_linTwo_cz h3 hL hz
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField p 2)ˣ)
  have hcardU : Nat.card (GaloisField p 2)ˣ = p ^ 2 - 1 := by
    rw [Nat.card_units, GaloisField.card p 2 (by norm_num)]
  obtain ⟨t, htK, htz, ht⟩ := htor μ
  set c : GaloisField p 2 := (μ : GaloisField p 2) ^ 2 with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Units.ne_zero μ)
  refine ⟨t, htK, htz, mem_normalizer_of_torus_conj φ hc0 ht, fun k hk Y hYX hY => ?_, ?_⟩
  · have htk := conj_pow_of_torus_conj φ ht k
    refine eq_bot_or_eq_of_torus_conj' (by norm_num) φ (γ := c ^ k) (fun d hd0 hd2 h => ?_)
      (pow_ne_zero _ hc0) htk hYX hY
    have hd1 : d = 1 := by omega
    subst hd1
    apply hk
    have h1 : μ ^ (2 * k * (p - 1)) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have e : (c ^ k) ^ (p ^ 1 - 1) = (μ : GaloisField p 2) ^ (2 * k * (p - 1)) := by
        rw [hc, pow_one, ← pow_mul, ← pow_mul, mul_assoc]
      rw [← e]
      exact h
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hμ, hcardU] at h2
    exact half_succ_dvd_of_sq_sub_one_dvd hp hp2 h2
  · set k := (p + 1) / 2 with hk
    obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have h2k : 2 * k = p + 1 := by omega
    set γ : GaloisField p 2 := c ^ k with hγ
    have hγμ : γ = (μ : GaloisField p 2) ^ (p + 1) := by rw [hγ, hc, ← pow_mul, h2k]
    have hμ1 : (μ : GaloisField p 2) ^ (p ^ 2 - 1) = 1 := by
      have h := pow_orderOf_eq_one μ
      rw [hμ, hcardU] at h
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    have hsplit : (p + 1) * p = (p + 1) + (p ^ 2 - 1) := by
      zify [hp1]
      ring
    have hγp : γ ^ p = γ := by
      rw [hγμ, ← pow_mul, hsplit, pow_add, hμ1, mul_one]
    have hγbot : γ ∈ (⊥ : Subfield (GaloisField p 2)) :=
      (Subfield.mem_bot_iff_pow_eq_self (GaloisField p 2) p).mpr hγp
    rw [Subfield.bot_eq_of_zMod_algebra p] at hγbot
    obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp hγbot
    have hγl : γ = ((a.val : ℕ) : GaloisField p 2) := by
      have h1 : algebraMap (ZMod p) (GaloisField p 2) ((a.val : ℕ) : ZMod p) =
          ((a.val : ℕ) : GaloisField p 2) := map_natCast _ _
      rw [ZMod.natCast_zmod_val] at h1
      rw [← ha, h1]
    have hγ1 : γ ≠ 1 := by
      intro h1
      have h1' : μ ^ (p + 1) = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one, ← hγμ, h1])
      have hdvd := orderOf_dvd_of_pow_eq_one h1'
      rw [hμ, hcardU] at hdvd
      have hle := Nat.le_of_dvd (by omega) hdvd
      have : p + 1 < p ^ 2 - 1 := by
        have : 5 * p ≤ p ^ 2 := by nlinarith
        omega
      omega
    have hγ0 : γ ≠ 0 := pow_ne_zero _ hc0
    have hl0 : a.val ≠ 0 := fun h => hγ0 (by rw [hγl, h, Nat.cast_zero])
    have hl1 : a.val ≠ 1 := fun h => hγ1 (by rw [hγl, h, Nat.cast_one])
    have hlt : a.val < p := ZMod.val_lt a
    refine ⟨a.val, by omega, ?_, fun x hx => ?_⟩
    · exact (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    · obtain ⟨b, hb⟩ := φ.surjective ⟨x, hx⟩
      have hxb : (φ b : G) = x := congrArg Subtype.val hb
      rw [← hxb, conj_pow_of_torus_conj φ ht k]
      have hpow : ((φ b : d1LiftX p H R K) : G) ^ a.val =
          ((φ (b ^ a.val) : d1LiftX p H R K) : G) := by
        rw [map_pow]
        rfl
      rw [hpow]
      congr 2
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd, toAdd_pow, nsmul_eq_mul, ← hγ, hγl]

end CFSG.AGLEmbedding
