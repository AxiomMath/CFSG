module

public import CFSG.LocalAnalysis.GLTheoremA.S8.I1425ON
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.HNRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Dickson.I271



@[expose] def UniqComp {Y : Type} [Group Y] (C A : Subgroup Y) : Prop :=
  GLAPComponent 3 C A ∧ ∀ I : Subgroup Y, GLAPComponent 3 C I → I = A

theorem map_facts {P Y : Type} [Group P] [Group Y] (φ : P →* Y) (hφ : Function.Injective φ)
    {C A Z : Subgroup P} (hAn : ∀ g ∈ C, ∀ l ∈ A, g * l * g⁻¹ ∈ A)
    (hcen : C ⊓ Subgroup.centralizer (A : Set P) ≤ Z) :
    (∀ g ∈ C.map φ, ∀ l ∈ A.map φ, g * l * g⁻¹ ∈ A.map φ) ∧
      C.map φ ⊓ Subgroup.centralizer ((A.map φ : Subgroup Y) : Set Y) ≤ Z.map φ := by
  constructor
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨l, hl, rfl⟩
    exact ⟨g * l * g⁻¹, hAn g hg l hl, by simp⟩
  · rintro _ ⟨⟨c, hc, rfl⟩, hcA⟩
    refine ⟨c, hcen ⟨hc, ?_⟩, rfl⟩
    have hcA' : φ c ∈ Subgroup.centralizer ((A.map φ : Subgroup Y) : Set Y) := hcA
    show c ∈ Subgroup.centralizer (A : Set P)
    rw [Subgroup.mem_centralizer_iff] at hcA' ⊢
    intro a ha
    exact hφ (by rw [map_mul, map_mul]; exact hcA' _ ⟨a, ha, rfl⟩)

theorem uniqComp_of_normal {Y : Type} [Group Y] [Finite Y] {C A : Subgroup Y} (hAC : A ≤ C)
    (hAn : ∀ g ∈ C, ∀ l ∈ A, g * l * g⁻¹ ∈ A) (hAq : CFSG.Open.IsQuasisimple ↥A)
    (hpA : 3 ∣ Nat.card ↥A) (hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (A : Set Y))) :
    UniqComp C A := by
  have hcore := glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three hAC hAn hAq hpA hcent
  exact ⟨glaPComponent_of_normal_quasisimple hAC hAn hAq hcore,
    fun I hI => eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three hAC hAn hAq hcore hcent hI⟩

theorem centralizer_map_equiv {Q Y : Type} [Group Q] [Group Y] (ψ : Q ≃* Y) (q : Q) :
    Subgroup.centralizer ({ψ q} : Set Y) = (Subgroup.centralizer ({q} : Set Q)).map ψ.toMonoidHom := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨ψ.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hx]

theorem inf_normalizer_map {P Y : Type} [Group P] [Group Y] (φ : P →* Y) (hφ : Function.Injective φ)
    {C V : Subgroup P} {D : Subgroup Y} (hD : D = C.map φ) :
    D ⊓ Subgroup.normalizer ((V.map φ : Subgroup Y) : Set Y) =
      (C ⊓ Subgroup.normalizer (V : Set P)).map φ := by
  subst hD
  apply le_antisymm
  · rintro _ ⟨⟨c, hc, rfl⟩, hN⟩
    refine ⟨c, ⟨hc, ?_⟩, rfl⟩
    have hN' : φ c ∈ Subgroup.normalizer ((V.map φ : Subgroup Y) : Set Y) := hN
    show c ∈ Subgroup.normalizer (V : Set P)
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have h := (Subgroup.mem_normalizer_iff.1 hN') (φ v)
    rw [Subgroup.mem_map_iff_mem hφ, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hφ] at h
    exact h
  · exact le_inf (Subgroup.map_mono inf_le_left)
      ((Subgroup.map_mono inf_le_right).trans (Subgroup.le_normalizer_map _))


variable {Λ : Type} [Group Λ] [Finite Λ]





theorem exists_mem_normalizer_mk_eq_of_bound {p : ℕ} (hp : p.Prime) (N : Subgroup Λ) [N.Normal]
    {P : Subgroup Λ} (hP : IsPGroup p P)
    (hbound : ∀ S : Subgroup Λ, S ≤ (P.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) →
      IsPGroup p S → Nat.card S ≤ Nat.card P) {g : Λ}
    (hg : QuotientGroup.mk' N g ∈ Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Set (Λ ⧸ N))) :
    ∃ n ∈ Subgroup.normalizer (P : Set Λ), QuotientGroup.mk' N n = QuotientGroup.mk' N g := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' N
  set M : Subgroup Λ := (P.map π).comap π with hM
  have hPM : P ≤ M := fun x hx => Subgroup.mem_map_of_mem π hx
  set Pg : Subgroup Λ := P.map (MulAut.conj g).toMonoidHom with hPg
  have hPgM : Pg ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    show π (g * x * g⁻¹) ∈ P.map π
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg (π x)).mp (Subgroup.mem_map_of_mem π hx)
  have hPgp : IsPGroup p Pg := hP.map _
  have hPgcard : Nat.card Pg = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hsyl : ∀ S : Subgroup Λ, S ≤ M → IsPGroup p S → Nat.card S = Nat.card P →
      ∃ T : Sylow p M, (T : Subgroup M) = S.subgroupOf M := by
    intro S hSM hS hScard
    have hS' : IsPGroup p (S.subgroupOf M) :=
      hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
    obtain ⟨T, hT⟩ := hS'.exists_le_sylow
    refine ⟨T, (Subgroup.eq_of_le_of_card_ge hT ?_).symm⟩
    have h1 : Nat.card ((T : Subgroup M).map M.subtype) ≤ Nat.card P :=
      hbound _ (Subgroup.map_subtype_le _) (T.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective M.subtype_injective] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, hScard]
    exact h1
  obtain ⟨T1, hT1⟩ := hsyl P hPM hP rfl
  obtain ⟨T2, hT2⟩ := hsyl Pg hPgM hPgp hPgcard
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M T2 T1
  have hcg : (c : Λ) * g ∈ Subgroup.normalizer (P : Set Λ) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hyM : g * x * g⁻¹ ∈ M := hPgM ⟨x, hx, rfl⟩
      have hy : (⟨g * x * g⁻¹, hyM⟩ : M) ∈ (T2 : Subgroup M) := by
        rw [hT2]
        exact Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
      have hmem : c * ⟨g * x * g⁻¹, hyM⟩ * c⁻¹ ∈ (T1 : Subgroup M) := by
        rw [← hc]
        show _ ∈ ((c • T2 : Sylow p M) : Subgroup M)
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        convert hy using 1
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
        group
      rw [hT1, Subgroup.mem_subgroupOf] at hmem
      have heq : ((c * ⟨g * x * g⁻¹, hyM⟩ * c⁻¹ : M) : Λ) =
          (MulAut.conj ((c : Λ) * g)) x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply]
        group
      change (MulAut.conj ((c : Λ) * g)) x ∈ P
      rw [← heq]
      exact hmem
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp c.2
  refine ⟨x⁻¹ * ((c : Λ) * g), Subgroup.mul_mem _ (Subgroup.inv_mem _
    (Subgroup.le_normalizer hx)) hcg, ?_⟩
  rw [map_mul, map_mul, map_inv, hxc, inv_mul_cancel_left]

theorem card_le_of_isPGroup {q : ℕ} (hq : q.Prime) {Q S : Subgroup Λ} (hSQ : S ≤ Q)
    (hS : IsPGroup q S) : Nat.card S ≤ q ^ (Nat.card Q).factorization q := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdvd : Nat.card S ∣ Nat.card Q := Subgroup.card_dvd_of_le hSQ
  rw [hk] at hdvd ⊢
  have := (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  exact Nat.pow_le_pow_right hq.pos this

theorem isElemAbelian_zpowers {Q : Type*} [Group Q] {g : Q} (hg : g ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers g) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · intro z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem lift_data (N : Subgroup Λ) [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {yb : Λ ⧸ N} (hyb : orderOf yb = 3) {Tb : Subgroup (Λ ⧸ N)} (hT2 : IsPGroup 2 Tb) (hT1 : Tb ≠ ⊥)
    (hyT : yb ∈ Subgroup.normalizer (Tb : Set (Λ ⧸ N))) :
    ∃ (y : Λ) (T : Subgroup Λ), QuotientGroup.mk' N y = yb ∧ orderOf y = 3 ∧ IsPGroup 2 T ∧
      T ≠ ⊥ ∧ y ∈ Subgroup.normalizer (T : Set Λ) ∧ T.map (QuotientGroup.mk' N) = Tb ∧
      (Subgroup.centralizer ({y} : Set Λ)).map (QuotientGroup.mk' N) =
        Subgroup.centralizer ({yb} : Set (Λ ⧸ N)) ∧
      (Subgroup.centralizer ({y} : Set Λ) ⊓ Subgroup.normalizer (T : Set Λ)).map
          (QuotientGroup.mk' N) =
        Subgroup.centralizer ({yb} : Set (Λ ⧸ N)) ⊓ Subgroup.normalizer (Tb : Set (Λ ⧸ N)) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hyb3 : yb ^ 3 = 1 := by rw [← hyb]; exact pow_orderOf_eq_one yb
  obtain ⟨S, hSle, hSel, hScard⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift N hN (isElemAbelian_zpowers hyb3)
  have hSp : IsPGroup 3 S := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact hSel.2 _ x.2)⟩
  have hSmap : S.map π = Subgroup.zpowers yb := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 hSle) ?_
    have h := Nat.card_image_of_injOn (S8.L84.injOn_mk_of_isPGroup hp3 N hN hSp)
    rw [← Subgroup.coe_map] at h
    have h' : Nat.card (S.map π) = Nat.card S := h
    rw [h', hScard]
  obtain ⟨y, hyS, hyπ⟩ : ∃ y ∈ S, π y = yb := by
    have : yb ∈ S.map π := by rw [hSmap]; exact Subgroup.mem_zpowers yb
    obtain ⟨y, hy, h⟩ := this
    exact ⟨y, hy, h⟩
  have hy3 : y ^ 3 = 1 := hSel.2 y hyS
  have hyo : orderOf y = 3 := by
    refine orderOf_eq_prime hy3 fun h => ?_
    rw [h, map_one] at hyπ
    rw [← hyπ, orderOf_one] at hyb
    exact absurd hyb (by norm_num)
  have hyp : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy3
  have hC : (Subgroup.centralizer ({y} : Set Λ)).map π = Subgroup.centralizer ({yb} : Set (Λ ⧸ N)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N hN (Subgroup.zpowers y) hyp
    rw [MonoidHom.map_zpowers, S8.L84.centralizer_zpowers_eq_singleton,
      S8.L84.centralizer_zpowers_eq_singleton] at h
    rw [← hyπ]
    exact h
  set Tt : Subgroup Λ := Tb.comap π with hTt
  have hTtcard : Nat.card Tt = Nat.card N * Nat.card Tb :=
    QuotientGroup.card_preimage_mk N (Tb : Set (Λ ⧸ N))
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hT1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  have hTtcop : Nat.Coprime 3 (Nat.card Tt) := by
    rw [hTtcard, hk]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp3).2 hN)
      (Nat.Coprime.pow_right k (by norm_num))
  have h2Tt : 2 ∣ Nat.card Tt := by
    rw [hTtcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hyTt : y ∈ Subgroup.normalizer (Tt : Set Λ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have h := (Subgroup.mem_normalizer_iff.1 hyT) (π t)
    show π t ∈ Tb ↔ π (y * t * y⁻¹) ∈ Tb
    rw [map_mul, map_mul, map_inv, hyπ]
    exact h
  obtain ⟨T, hTTt, hT2', hT1', hyNT, hTcard⟩ :=
    S3.exists_invariant_sylow hp3 Nat.prime_two hyp (Subgroup.zpowers_le.2 hyTt) hTtcop h2Tt
  have hyN : y ∈ Subgroup.normalizer (T : Set Λ) := hyNT (Subgroup.mem_zpowers y)
  have hTmap : T.map π = Tb := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_iff_le_comap.2 hTTt) ?_
    have hkr := Subgroup.card_ker_mul_card_range (π.comp T.subtype)
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at hkr
    have hkerN : ((π.comp T.subtype).ker).map T.subtype ≤ N := by
      rintro _ ⟨u, hu, rfl⟩
      have hu' : π (u : Λ) = 1 := hu
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hu'
      exact hu'
    have hkerp : IsPGroup 2 ((π.comp T.subtype).ker.map T.subtype) := hT2'.to_le (Subgroup.map_subtype_le _)
    have hb := card_le_of_isPGroup Nat.prime_two hkerN hkerp
    rw [Subgroup.card_map_of_injective T.subtype_injective] at hb
    have hn0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
    have hf : (Nat.card N * 2 ^ k).factorization 2 = (Nat.card N).factorization 2 + k := by
      simp [Nat.factorization_mul hn0 (pow_ne_zero _ two_ne_zero), Nat.factorization_pow,
        Nat.prime_two.factorization_self]
    rw [hTcard, hTtcard, hk, hf, pow_add] at hkr
    rw [hk]
    have hpos : 0 < 2 ^ (Nat.card N).factorization 2 := by positivity
    by_contra hlt
    push_neg at hlt
    have h1 := Nat.mul_le_mul hb (le_refl (Nat.card ↥(T.map π)))
    have h2 := Nat.mul_lt_mul_of_pos_left hlt hpos
    linarith
  refine ⟨y, T, hyπ, hyo, hT2', hT1', hyN, hTmap, hC, le_antisymm ?_ ?_⟩
  · refine le_inf ((Subgroup.map_mono inf_le_left).trans hC.le) ?_
    rw [← hTmap]
    exact (Subgroup.map_mono inf_le_right).trans (Subgroup.le_normalizer_map _)
  · rintro mb ⟨hmC, hmN⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N mb
    have hbound : ∀ S : Subgroup Λ, S ≤ (T.map π).comap π → IsPGroup 2 S →
        Nat.card S ≤ Nat.card T := by
      intro S hS hSp
      rw [hTmap] at hS
      rw [hTcard]
      exact card_le_of_isPGroup Nat.prime_two hS hSp
    have hg : π m ∈ Subgroup.normalizer ((T.map π : Subgroup (Λ ⧸ N)) : Set (Λ ⧸ N)) := by
      rw [hTmap]; exact hmN
    obtain ⟨n, hn, hnm⟩ := exists_mem_normalizer_mk_eq_of_bound Nat.prime_two N hT2' hbound hg
    set NT := Subgroup.normalizer (T : Set Λ)
    set ψ : ↥NT →* Λ ⧸ N := π.comp NT.subtype
    have hker : ¬ 3 ∣ Nat.card ψ.ker := by
      intro h3
      apply hN
      refine h3.trans ?_
      rw [← Subgroup.card_map_of_injective NT.subtype_injective]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨u, hu, rfl⟩
      have hu' : π (u : Λ) = 1 := hu
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hu'
      exact hu'
    have hy' : IsPGroup 3 (Subgroup.zpowers (⟨y, hyN⟩ : NT)) :=
      isPGroup_zpowers_of_pow_eq_one (Subtype.ext (by simpa using hy3))
    obtain ⟨o, ho, hko⟩ := exists_mem_ker_mul_commute hp3 ψ hker hy' (k := ⟨n, hn⟩) (by
      show π n * π y = π y * π n
      rw [hnm, hyπ]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hmC))
    refine ⟨((⟨n, hn⟩ : NT) * o : NT), ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, (⟨n, hn⟩ * o : NT).2⟩, ?_⟩
    · have := congrArg Subtype.val hko
      simp only [Subgroup.coe_mul] at this ⊢
      exact this
    · have ho' : π (o : Λ) = 1 := ho
      show π ((n : Λ) * (o : Λ)) = π m
      rw [map_mul, ho', mul_one, hnm]


variable {G : Type} [Group G] [Finite G]





theorem uniq_lift {L H : Subgroup G} (hHL : H ≤ L) {I : Subgroup (PQuot 3 L)}
    (hU : UniqComp (barX 3 L H) I) :
    ∃ J : Subgroup G, UniqComp H J ∧ barX 3 L J = I ∧ Nonempty (PQuot 3 J ≃* PQuot 3 I) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hker := coprime_card_inf_ker_pQuotHom hp L (H.subgroupOf L)
  have hU1 : GLAPComponent 3 ((H.subgroupOf L).map (pQuotHom 3 L)) I := hU.1
  obtain ⟨K, hK, hKI⟩ := exists_glaPComponent_map_eq hp (pQuotHom 3 L) hker hU1
  have hsub : Nat.Coprime 3 (Nat.card ↥((H.subgroupOf L) ⊓ L.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hJ : GLAPComponent 3 H (K.map L.subtype) := by
    have h1 := glaPComponent_map hp L.subtype hsub hK
    rwa [Subgroup.map_subgroupOf_eq_of_le hHL] at h1
  have hKsub : (K.map L.subtype).subgroupOf L = K :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective K
  have hbar : barX 3 L (K.map L.subtype) = I := by
    show ((K.map L.subtype).subgroupOf L).map (pQuotHom 3 L) = I
    rw [hKsub]
    exact hKI
  refine ⟨K.map L.subtype, ⟨hJ, fun J' hJ' => ?_⟩, hbar, ?_⟩
  · have h1 := glaPComponent_subgroupOf hp hHL hJ'
    have h2 := glaPComponent_map hp (pQuotHom 3 L) hker h1
    have h3 : (J'.subgroupOf L).map (pQuotHom 3 L) = I := hU.2 _ h2
    have h4 : J'.subgroupOf L = K :=
      glaPComponent_eq_of_map_eq hp (pQuotHom 3 L) hker h1 hK (h3.trans hKI.symm)
    rw [← h4, Subgroup.map_subgroupOf_eq_of_le (hJ'.1.trans hHL)]
  · obtain ⟨e₁⟩ := nonempty_pQuot_equiv_imageMod hp (hJ.1.trans hHL)
    obtain ⟨e₂⟩ := nonempty_pQuot_equiv_of_eq (p := 3) (show imageMod 3 L (K.map L.subtype) = I from hbar)
    exact ⟨e₁.trans e₂⟩

theorem glaPPrimeCore_eq_bot_of_simple {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h3 : 3 ∣ Nat.card S) : GLAPPrimeCore 3 S = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 S)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := S)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 S) with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hcop
    exact absurd (hcop.eq_one_of_dvd h3) (by norm_num)

noncomputable def pQuotEquivSelf {Q : Type} [Group Q] [Finite Q] (I : Subgroup Q) [IsSimpleGroup I]
    (h3 : 3 ∣ Nat.card I) : PQuot 3 I ≃* I :=
  (QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_bot_of_simple h3)).trans
    QuotientGroup.quotientBot

theorem le_of_cover {H₁ H₂ I J : Subgroup G} (hH : H₂ ≤ H₁) (hJH : J ≤ H₁)
    (hJn : ∀ g ∈ H₁, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hI : GLAPComponent 3 H₂ I)
    (hs : IsSimpleGroup (PQuot 3 I)) (h3 : 3 ∣ Nat.card (PQuot 3 I))
    (hcov : ∀ i ∈ I, ∃ j ∈ J, Nat.Coprime 3 (orderOf (j⁻¹ * i))) : I ≤ J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hIH₁ : I ≤ H₁ := hI.1.trans hH
  have hJnorm : (J.subgroupOf H₁).Normal := normal_subgroupOf_of_conj hJn
  have h3el : ∀ i ∈ I, orderOf i = 3 → i ∈ J := by
    intro i hi hio
    obtain ⟨j, hj, hcop⟩ := hcov i hi
    set ρ := QuotientGroup.mk' (J.subgroupOf H₁)
    have hiH : i ∈ H₁ := hIH₁ hi
    have hjH : j ∈ H₁ := hJH hj
    have hρ : ρ ⟨i, hiH⟩ = ρ (⟨j, hjH⟩⁻¹ * ⟨i, hiH⟩) := by
      rw [map_mul, map_inv]
      have : ρ ⟨j, hjH⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hj
      rw [this, inv_one, one_mul]
    have hd1 : orderOf (ρ ⟨i, hiH⟩) ∣ 3 := by
      refine (orderOf_map_dvd ρ _).trans ?_
      rw [Subgroup.orderOf_mk, hio]
    have hd2 : orderOf (ρ ⟨i, hiH⟩) ∣ orderOf (j⁻¹ * i) := by
      rw [hρ]
      refine (orderOf_map_dvd ρ _).trans ?_
      rw [Subgroup.orderOf_mk]
      rfl
    have h1 : orderOf (ρ ⟨i, hiH⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.coprime_dvd_left hd2 hcop.symm)) hd1
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1
  set N : Subgroup G := I ⊓ J with hNdef
  have hNI : N ≤ I := inf_le_left
  have hNn : (N.subgroupOf I).Normal := normal_subgroupOf_of_conj fun g hg l hl =>
    ⟨I.mul_mem (I.mul_mem hg hl.1) (I.inv_mem hg), hJn g (hIH₁ hg) l hl.2⟩
  set σ := QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)
  have hNbn : ((N.subgroupOf I).map σ).Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  haveI := hs
  haveI := hNbn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf I).map σ) with hbot | htop
  · exfalso
    have h3I : 3 ∣ Nat.card I := h3.trans (by
      have := Subgroup.index_dvd_card (GLAPPrimeCore 3 ↥I)
      simpa [Subgroup.index] using this)
    obtain ⟨i, hio⟩ := exists_prime_orderOf_dvd_card' 3 h3I
    have hiJ : (i : G) ∈ J := h3el i i.2 (by rw [← Subgroup.orderOf_coe] at hio; exact hio)
    have hmem : σ i ∈ (N.subgroupOf I).map σ := ⟨i, ⟨i.2, hiJ⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hio] at hdvd
    exact absurd (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥I)) (by
      intro hc; exact absurd (hc.eq_one_of_dvd hdvd) (by norm_num))
  ·
    by_contra hnle
    have hlt : N < I := lt_of_le_of_ne hNI (fun h => hnle (h ▸ inf_le_right))
    have hsn : IsSubnormal N H₂ := IsSubnormal.step hNI hNn hI.2.1
    have hcore : GLAPPrimeCoreOf 3 I ≤ GLAPPrimeCoreOf 3 H₂ :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hI.2.1
    refine hI.2.2.2 N hlt hsn (le_antisymm (barX_mono 3 hNI) ?_)
    refine barX_le_of_forall (hNI.trans hI.1) fun k hk => ?_
    have hk' : σ ⟨k, hk⟩ ∈ (N.subgroupOf I).map σ := by rw [htop]; trivial
    obtain ⟨n, hn, hnk⟩ := hk'
    refine ⟨n, hn, hcore ⟨n⁻¹ * ⟨k, hk⟩, ?_, by simp⟩⟩
    exact (QuotientGroup.eq).1 hnk

end CFSG.LocalAnalysis.GLTheoremA.S8.HNRows
