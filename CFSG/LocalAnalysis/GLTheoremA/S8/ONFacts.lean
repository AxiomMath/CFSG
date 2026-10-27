module

public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016ONRow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONThree
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside

public section


namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open

variable {H : Type*} [Group H] [Finite H]

theorem injOn_mk_of_isPGroup {p : ℕ} (hp : p.Prime) (N : Subgroup H) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup H} (hP : IsPGroup p P) :
    Set.InjOn (QuotientGroup.mk' N) (P : Set H) := by
  have : Fact p.Prime := ⟨hp⟩
  intro x hx y hy hxy
  have hxyP : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
  have hxyN : x⁻¹ * y ∈ N := by
    rw [← QuotientGroup.ker_mk' N]
    show QuotientGroup.mk' N (x⁻¹ * y) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hNpow : (x⁻¹ * y) ^ Nat.card N = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x⁻¹ * y, hxyN⟩ : N)))
  have hPpow : (x⁻¹ * y) ^ Nat.card P = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x⁻¹ * y, hxyP⟩ : P)))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hcop : Nat.gcd (Nat.card P) (Nat.card N) = 1 := by
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  have h1 := (pow_gcd_eq_one (a := x⁻¹ * y) (m := Nat.card P) (n := Nat.card N)).2
    ⟨hPpow, hNpow⟩
  rw [hcop, pow_one, inv_mul_eq_one] at h1
  exact h1

theorem isElemAbelian_of_injOn {K : Type*} [Group K] {p : ℕ} (f : H →* K) {P : Subgroup H}
    (hinj : Set.InjOn f (P : Set H)) (h : IsElemAbelian p (P.map f)) : IsElemAbelian p P := by
  obtain ⟨hc, hx⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply hinj (P.mul_mem a.2 b.2) (P.mul_mem b.2 a.2)
    have h2 := congrArg Subtype.val (hc.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
    simpa [map_mul] using h2
  · apply hinj (P.pow_mem ha p) P.one_mem
    rw [map_pow, map_one]
    exact hx _ (Subgroup.mem_map_of_mem f ha)

theorem isElemAbelian_map {K : Type*} [Group K] {p : ℕ} (f : H →* K) {P : Subgroup H}
    (hP : IsElemAbelian p P) : IsElemAbelian p (P.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
    obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hP.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨a', ha', rfl⟩
    rw [← map_pow, hP.2 a' ha', map_one]

theorem exists_elemAbelian_le_of_quot {p k : ℕ} (hp : p.Prime) (N : Subgroup H) [N.Normal]
    (hN : ¬ p ∣ Nat.card N)
    (hS : ∀ S : Sylow p (H ⧸ N), IsElemAbelian p (S : Subgroup (H ⧸ N)) ∧ Nat.card S = p ^ k)
    {Q : Subgroup H} (hQ : IsPGroup p Q) :
    ∃ P : Subgroup H, Q ≤ P ∧ IsElemAbelian p P ∧ Nat.card P = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  set Pb := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) P with hPb
  have hcoe : (Pb : Subgroup (H ⧸ N)) = (P : Subgroup H).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective _ P
  have hinj := injOn_mk_of_isPGroup hp N hN P.isPGroup'
  obtain ⟨hab, hcard⟩ := hS Pb
  rw [hcoe] at hab hcard
  refine ⟨P, hQP, isElemAbelian_of_injOn _ hinj hab, ?_⟩
  have h := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at h
  rw [← hcard]
  exact h.symm

theorem exists_mem_normalizer_mk_eq {p : ℕ} (hp : p.Prime) (N : Subgroup H) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup H} (hP : IsPGroup p P) {g : H}
    (hg : QuotientGroup.mk' N g ∈ Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Set (H ⧸ N))) :
    ∃ n ∈ Subgroup.normalizer (P : Set H), QuotientGroup.mk' N n = QuotientGroup.mk' N g := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' N
  set M : Subgroup H := (P.map π).comap π with hM
  have hcardmap : ∀ S : Subgroup H, IsPGroup p S → Nat.card (S.map π) = Nat.card S := by
    intro S hS
    have h := Nat.card_image_of_injOn (injOn_mk_of_isPGroup hp N hN hS)
    rw [← Subgroup.coe_map] at h
    exact h
  have hbound : ∀ S : Subgroup H, S ≤ M → IsPGroup p S → Nat.card S ≤ Nat.card P := by
    intro S hSM hS
    rw [← hcardmap S hS, ← hcardmap P hP]
    exact Subgroup.card_le_of_le (Subgroup.map_le_iff_le_comap.mpr hSM)
  have hPM : P ≤ M := fun x hx => Subgroup.mem_map_of_mem π hx
  set Pg : Subgroup H := P.map (MulAut.conj g).toMonoidHom with hPg
  have hPgM : Pg ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    show π (g * x * g⁻¹) ∈ P.map π
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hg (π x)).mp (Subgroup.mem_map_of_mem π hx)
  have hPgp : IsPGroup p Pg := hP.map _
  have hPgcard : Nat.card Pg = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hsyl : ∀ S : Subgroup H, S ≤ M → IsPGroup p S → Nat.card S = Nat.card P →
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
  have hcg : (c : H) * g ∈ Subgroup.normalizer (P : Set H) := by
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
      have heq : ((c * ⟨g * x * g⁻¹, hyM⟩ * c⁻¹ : M) : H) =
          (MulAut.conj ((c : H) * g)) x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conj_apply]
        group
      change (MulAut.conj ((c : H) * g)) x ∈ P
      rw [← heq]
      exact hmem
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp c.2
  refine ⟨x⁻¹ * ((c : H) * g), Subgroup.mul_mem _ (Subgroup.inv_mem _
    (Subgroup.le_normalizer hx)) hcg, ?_⟩
  rw [map_mul, map_mul, map_inv, hxc, inv_mul_cancel_left]

theorem exists_normalizer_conj_of_quot {p : ℕ} (hp : p.Prime) (N : Subgroup H) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) {P : Subgroup H} (hP : IsPGroup p P) {h h' : H} (hh : h ∈ P)
    (hh' : h' ∈ P) {nb : H ⧸ N}
    (hnb : nb ∈ Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Set (H ⧸ N)))
    (hconj : nb * QuotientGroup.mk' N h * nb⁻¹ = QuotientGroup.mk' N h') :
    ∃ n ∈ Subgroup.normalizer (P : Set H), n * h * n⁻¹ = h' := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N nb
  obtain ⟨n, hn, hng⟩ := exists_mem_normalizer_mk_eq hp N hN hP hnb
  refine ⟨n, hn, injOn_mk_of_isPGroup hp N hN hP
    ((Subgroup.mem_normalizer_iff.mp hn h).mp hh) hh' ?_⟩
  rw [map_mul, map_mul, map_inv, hng, hconj]

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem fixes_of_outer_dvd_two {Y : Type*} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    (hOut : Nat.card (Outer Y) ∣ 2) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Sylow p Y)
    (hS : ∀ a ∈ (S : Subgroup Y), ∀ b ∈ (S : Subgroup Y), a * b = b * a) (σ : MulAut Y) {k : ℕ}
    (hσ : σ ^ p ^ k = 1) (hσS : ∀ s ∈ (S : Subgroup Y), σ s ∈ (S : Subgroup Y)) :
    ∀ s ∈ (S : Subgroup Y), σ s = s := by
  have hp := (Fact.out : p.Prime)
  have hinn : σ ∈ inner Y := by
    set ψ : Outer Y := QuotientGroup.mk σ
    have h1 : orderOf ψ ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one])
    have h2 : orderOf ψ ∣ 2 := (orderOf_dvd_natCard ψ).trans hOut
    have h3 : orderOf ψ = 1 := by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp h1
      rcases m with _ | m
      · simpa using hm
      · exfalso
        have : p ∣ 2 := (dvd_pow_self p (Nat.succ_ne_zero m)).trans (hm ▸ h2)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    rw [orderOf_eq_one_iff] at h3
    exact (QuotientGroup.eq_one_iff σ).mp h3
  obtain ⟨y, rfl⟩ := hinn
  have hy : y ^ p ^ k = 1 := by
    have h : MulAut.conj (y ^ p ^ k) = 1 := by rw [map_pow]; exact hσ
    have hc : y ^ p ^ k ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut Y => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * y ^ p ^ k = y ^ p ^ k * g * (y ^ p ^ k)⁻¹ * y ^ p ^ k := by rw [this]
        _ = y ^ p ^ k * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact hσS s hs
    · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hyp : IsPGroup p (Subgroup.zpowers y) := fun g => ⟨k, by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy,
      one_zpow]
    rfl⟩
  have hsup : IsPGroup p ↥(Subgroup.zpowers y ⊔ (S : Subgroup Y)) :=
    hyp.to_sup_of_normal_right' S.isPGroup' hyN
  have hyS : y ∈ (S : Subgroup Y) := by
    rw [← S.is_maximal' hsup le_sup_right]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  intro s hs
  rw [MulAut.conj_apply, hS y hyS s hs, mul_inv_cancel_right]

section ON

theorem sylow_three_ON
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* CFSG.Blueprint.NativeSporadic.ON) (S : Sylow 3 Y) :
    IsElemAbelian 3 (S : Subgroup Y) ∧ Nat.card (S : Subgroup Y) = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_sylow_elemAbelian_ON Y e
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y T S
  refine ⟨?_, ?_⟩
  · have hmap : ((g • T : Sylow 3 Y) : Subgroup Y) = (T : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
      ext x
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hx
        refine ⟨_, hx, ?_⟩
        rw [MulAut.smul_def, ← map_inv]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨y, hy, rfl⟩
        have h : (MulAut.conj g)⁻¹ • ((MulAut.conj g).toMonoidHom y) = y := by
          rw [MulAut.smul_def, ← map_inv]
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [h]
        exact hy
    rw [hmap]
    exact isElemAbelian_map _ hT
  · rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      CFSG.RankThree.Native.factorization_card_ON]

theorem sylow_three_fusion_ON
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* CFSG.Blueprint.NativeSporadic.ON) (S : Sylow 3 Y)
    {s s' : Y} (hs : s ∈ (S : Subgroup Y)) (hs1 : s ≠ 1) (hs' : s' ∈ (S : Subgroup Y))
    (hs'1 : s' ≠ 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y), n * s * n⁻¹ = s' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hab, hcard⟩ := sylow_three_ON e S
  have ho : ∀ x ∈ (S : Subgroup Y), x ≠ 1 → orderOf (e x) = 3 := fun x hx hx1 => by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (hab.2 x hx) hx1
  obtain ⟨k, hk⟩ := CFSG.RankThree.Native.onThree_fusion (ho s hs hs1) (ho s' hs' hs'1)
  have hk' : e.symm k * s * (e.symm k)⁻¹ = s' := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hk]
  have hcomm : ∀ a ∈ (S : Subgroup Y), ∀ b ∈ (S : Subgroup Y), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨n, hn, hns⟩ := CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion S S le_rfl hcomm
    (fun g hg => Subgroup.eq_of_le_of_card_ge hg (by
      rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]))
    hs (hk' ▸ hs')
  exact ⟨n, hn, hns.trans hk'⟩

end ON

section Row

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_subgroupOf {L K : Subgroup G} (hKL : K ≤ L) {n : ↥L}
    (hn : n ∈ Subgroup.normalizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (n : G) ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := (Subgroup.mem_normalizer_iff.mp hn ⟨x, hKL hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp this
  · intro hx
    have hxL : x ∈ L := by
      have h1 : (n : G) * x * (n : G)⁻¹ ∈ L := hKL hx
      have h2 : x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * n := by group
      rw [h2]
      exact L.mul_mem (L.mul_mem (L.inv_mem n.2) h1) n.2
    exact Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hn ⟨x, hxL⟩).mpr (Subgroup.mem_subgroupOf.mpr hx))

theorem onFactsAt_holds
    (G : Type) [Group G] [Finite G] : ONFactsAt G := by
  intro X L hL hTW
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.card_eq_one.mp hTW.2
  obtain ⟨e⟩ := nonempty_pquot_equiv_ON hTW.1 hZ
  have hOut := CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨e⟩
  have hN : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) := by
    have h := not_dvd_card_glaPPrimeCoreOf hp3 L
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
  set π : ↥L →* PQuot 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hπ
  refine ⟨fun Q hQL hQ => ?_, fun H hHL hH hHcard => ?_⟩
  ·
    obtain ⟨P, hQP, hPe, hPc⟩ := exists_elemAbelian_le_of_quot hp3 (GLAPPrimeCore 3 ↥L) hN
      (sylow_three_ON e) (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm)
    refine ⟨P.map L.subtype, fun x hx => ⟨⟨x, hQL hx⟩, hQP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩,
      Subgroup.map_subtype_le _, isElemAbelian_map _ hPe, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hPc]
  set H' : Subgroup ↥L := H.subgroupOf L with hH'
  have hH'e : IsElemAbelian 3 H' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (hH.2 _ hx)⟩
    simpa using congrArg Subtype.val (hH.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  have hH'p : IsPGroup 3 H' := fun g => ⟨1, Subtype.ext (by simpa using hH'e.2 g g.2)⟩
  have hinj := injOn_mk_of_isPGroup hp3 (GLAPPrimeCore 3 ↥L) hN hH'p
  have hH'card : Nat.card H' = 3 ^ 4 := by
    rw [hH', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv, hHcard]
  have hHbcard : Nat.card (H'.map π) = 3 ^ 4 := by
    have h := Nat.card_image_of_injOn hinj
    rw [← Subgroup.coe_map] at h
    exact h.trans hH'card
  set SH : Sylow 3 (PQuot 3 L) := Sylow.ofCard (H'.map π) (by
    rw [hHbcard, Nat.card_congr e.toEquiv, CFSG.RankThree.Native.factorization_card_ON])
  have hSH : (SH : Subgroup (PQuot 3 L)) = H'.map π := Sylow.coe_ofCard _ _
  refine ⟨fun h hh h1 h' hh' h'1 => ?_, fun g hgL hgH ⟨k, hk⟩ => ?_⟩
  ·
    have hx : (⟨h, hHL hh⟩ : ↥L) ∈ H' := Subgroup.mem_subgroupOf.mpr hh
    have hx' : (⟨h', hHL hh'⟩ : ↥L) ∈ H' := Subgroup.mem_subgroupOf.mpr hh'
    have hne : ∀ y : ↥L, y ∈ H' → (y : G) ≠ 1 → π y ≠ 1 := fun y hy hy1 hπy => hy1 (by
      have := hinj hy H'.one_mem (hπy.trans (map_one π).symm)
      rw [this]; rfl)
    obtain ⟨nb, hnb, hnbc⟩ := sylow_three_fusion_ON e SH
      (hSH ▸ Subgroup.mem_map_of_mem π hx) (hne _ hx h1)
      (hSH ▸ Subgroup.mem_map_of_mem π hx') (hne _ hx' h'1)
    rw [hSH] at hnb
    obtain ⟨n, hn, hnc⟩ := exists_normalizer_conj_of_quot hp3 (GLAPPrimeCore 3 ↥L) hN hH'p hx hx'
      hnb hnbc
    exact ⟨n, n.2, mem_normalizer_of_subgroupOf hHL hn, congrArg Subtype.val hnc⟩
  ·
    set γ : ↥(Subgroup.normalizer (L : Set G)) := ⟨g, hgL⟩
    set σ := CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L γ
    have hγ : ∀ y : ↥L, (((L.normalizerMonoidHom γ) y : ↥L) : G) = g * y * g⁻¹ := fun y => rfl
    have hσ : σ ^ 3 ^ k = 1 := by
      have : γ ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [← map_pow, this, map_one]
    have hσy : ∀ y : ↥L, y ∈ H' → (L.normalizerMonoidHom γ) y ∈ H' := fun y hy => by
      rw [Subgroup.mem_subgroupOf, hγ]
      exact (Subgroup.mem_normalizer_iff.mp hgH y).mp (Subgroup.mem_subgroupOf.mp hy)
    have hσS : ∀ z ∈ (SH : Subgroup (PQuot 3 L)), σ z ∈ (SH : Subgroup (PQuot 3 L)) := by
      rw [hSH]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨_, hσy y hy, (CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 3 L γ y).symm⟩
    have hcomm : ∀ a ∈ (SH : Subgroup (PQuot 3 L)), ∀ b ∈ (SH : Subgroup (PQuot 3 L)),
        a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val ((sylow_three_ON e SH).1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hfix := fixes_of_outer_dvd_two hZ hOut (by norm_num) SH hcomm σ hσ hσS
    rw [Subgroup.mem_centralizer_iff]
    intro x hxH
    set y : ↥L := ⟨x, hHL hxH⟩
    have hy : y ∈ H' := Subgroup.mem_subgroupOf.mpr hxH
    have h1 := hfix (π y) (hSH ▸ Subgroup.mem_map_of_mem π hy)
    have h2 : π ((L.normalizerMonoidHom γ) y) = π y :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk 3 L γ y).symm.trans h1
    have h3 := congrArg Subtype.val (hinj (hσy y hy) hy h2)
    rw [hγ] at h3
    calc x * g = g * x * g⁻¹ * g := by rw [h3]
      _ = g * x := by group

end Row

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
