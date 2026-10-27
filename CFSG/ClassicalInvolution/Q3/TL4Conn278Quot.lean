module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quat
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]

omit [Finite G] in
theorem map_sup_normal_eq (L : Subgroup G) :
    (L ⊔ N).map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

theorem exists_conj_le_of_le_sup (hN : Odd (Nat.card N)) {L D : Subgroup G} (hD : IsPGroup 2 D)
    (hDL : D ≤ L ⊔ N) : ∃ ν ∈ N, conjSub ν D ≤ L := by
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := L) (IsPGroup.of_bot (p := 2)) bot_le
  have hPLN : IsSylow2In P (L ⊔ N) := by
    obtain ⟨Q, hQ, hPQ⟩ := IsSylow2In.exists_ge hP.2.1 (hP.1.trans le_sup_left)
    have hcardQ := natCard_eq_pow_of_isSylow2In hQ
    have hcardP := natCard_eq_pow_of_isSylow2In hP
    have hv : (Nat.card ↥(L ⊔ N)).factorization 2 = (Nat.card ↥L).factorization 2 := by
      have e1 := factorization_two_natCard_map_mk (N := N) hN (L ⊔ N)
      have e2 := factorization_two_natCard_map_mk (N := N) hN L
      rw [← e1, ← e2, map_sup_normal_eq]
    have hQP : Q = P :=
      (Subgroup.eq_of_le_of_card_ge hPQ (by rw [hcardQ, hcardP, hv])).symm
    rw [← hQP]
    exact hQ
  obtain ⟨Q, hQ, hDQ⟩ := IsSylow2In.exists_ge hD hDL
  obtain ⟨g, hg, hgQ⟩ := Thompson.exists_conj_of_isSylow2In hQ hPLN
  have hg' : g ∈ ((L ⊔ N : Subgroup G) : Set G) := hg
  rw [Subgroup.mul_normal] at hg'
  obtain ⟨l, hl, ν, hν, rfl⟩ := hg'
  refine ⟨ν, hν, ?_⟩
  have h1 : conjSub ν Q = conjSub l⁻¹ P := by
    rw [← hgQ, conjSub_mul, conjSub_inv_conjSub]
  calc conjSub ν D ≤ conjSub ν Q := conjSub_mono hDQ
    _ = conjSub l⁻¹ P := h1
    _ ≤ conjSub l⁻¹ L := conjSub_mono hP.1
    _ = L := conjSub_eq_self_of_mem (L.inv_mem hl)

omit [Finite G] in
theorem map_inf_sup_eq (L M : Subgroup G) :
    ((L ⊔ N) ⊓ (M ⊔ N)).map (QuotientGroup.mk' N) =
      L.map (QuotientGroup.mk' N) ⊓ M.map (QuotientGroup.mk' N) := by
  have hL : (L.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = L ⊔ N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hM : (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = M ⊔ N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [← hL, ← hM, ← Subgroup.comap_inf,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]

theorem exists_conj_pow_dvd_inf (hN : Odd (Nat.card N)) (L M : Subgroup G) :
    ∃ ν ∈ N, 2 ^ (Nat.card ↥(L.map (QuotientGroup.mk' N) ⊓
      M.map (QuotientGroup.mk' N))).factorization 2 ∣ Nat.card ↥(L ⊓ conjSub ν M) := by
  obtain ⟨D, hD, -⟩ := IsSylow2In.exists_ge (P := (L ⊔ N) ⊓ (M ⊔ N))
    (IsPGroup.of_bot (p := 2)) bot_le
  have hDc := natCard_eq_pow_of_isSylow2In hD
  have hv : (Nat.card ↥(L.map (QuotientGroup.mk' N) ⊓ M.map (QuotientGroup.mk' N))).factorization
      2 = (Nat.card ↥((L ⊔ N) ⊓ (M ⊔ N))).factorization 2 := by
    rw [← map_inf_sup_eq L M]
    exact factorization_two_natCard_map_mk hN _
  obtain ⟨ν₁, hν₁, h1⟩ := exists_conj_le_of_le_sup hN hD.2.1 (hD.1.trans inf_le_left)
  obtain ⟨ν₂, hν₂, h2⟩ := exists_conj_le_of_le_sup hN hD.2.1 (hD.1.trans inf_le_right)
  refine ⟨ν₁ * ν₂⁻¹, N.mul_mem hν₁ (N.inv_mem hν₂), ?_⟩
  have hE : conjSub ν₁ D ≤ L ⊓ conjSub (ν₁ * ν₂⁻¹) M := by
    refine le_inf h1 ?_
    have : conjSub ν₁ D = conjSub (ν₁ * ν₂⁻¹) (conjSub ν₂ D) := by
      rw [← conjSub_mul, inv_mul_cancel_right]
    rw [this]
    exact conjSub_mono h2
  have hcE : Nat.card ↥(conjSub ν₁ D) = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj ν₁).injective
  rw [hv, ← hDc, ← hcE]
  exact Subgroup.card_dvd_of_le hE


section Members

variable {r : ℕ} {Λ : Set (Subgroup G)}

omit [Finite G] in
theorem TypeRFam.closure_twoElts (h : TypeRFam r Λ) {L : Subgroup G} (hL : L ∈ Λ) :
    Subgroup.closure {x : G | x ∈ L ∧ IsPGroup 2 (Subgroup.zpowers x)} = L := by
  rcases h.hyp.omega2 L hL with h1 | he
  · exact h1
  · exfalso
    obtain ⟨e⟩ := he
    have h3 : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
      (h.twoGroup L hL).of_equiv e
    obtain ⟨k, hk⟩ := h3.exists_card_eq
    rw [natCard_sl2Three] at hk
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hk ▸ (by norm_num : 3 ∣ 24))
    omega

omit [Finite G] in
theorem TypeRFam.le_centralizer (h : TypeRFam r Λ) {L : Subgroup G} (hL : L ∈ Λ) {z : G}
    (hz : IsUniqueInvolution L z) : L ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨w, hwL, hw2, hsub⟩ := h.cls.subnormal L hL
  have hwsq : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hw : w = z := by
    rcases hz.unique w hwL hwsq with h1 | h1
    · rw [h1, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    · exact h1
  rw [← hw]
  exact isSubnormal_le hsub

omit [Finite G] in
theorem TypeRFam.mk_mem_normalizer (h : TypeRFam r Λ) (hN : Odd (Nat.card N)) {L : Subgroup G}
    (hL : L ∈ Λ) {z : G} (hz : IsUniqueInvolution L z) {g : G}
    (hg : QuotientGroup.mk' N g * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N g) :
    QuotientGroup.mk' N g ∈
      Subgroup.normalizer ((L.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
  have hsq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hmk : QuotientGroup.mk' N z = QuotientGroup.mk' N (g * z * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, hg]
    group
  obtain ⟨ν, hν, hνz⟩ := exists_conj_eq_of_map_eq hN hz.sq hsq hmk
  have hc : ν * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ν * g * z = (ν * (g * z * g⁻¹) * ν⁻¹) * (ν * g) := by group
      _ = z * (ν * g) := by rw [hνz]
  have hn := mk_mem_normalizer_map (N := N) (h.tight L hL z hz hc)
  have hνmk : QuotientGroup.mk' N ν = 1 := (QuotientGroup.eq_one_iff _).mpr hν
  rwa [map_mul, hνmk, one_mul] at hn

noncomputable def sylowMapEquiv (hN : Odd (Nat.card N)) {L P : Subgroup G} (hP : IsSylow2In P L) :
    ↥P ≃* ↥(P.map (QuotientGroup.mk' N)) :=
  AscQuot.quotRestrictEquiv
    (AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP.2.1 hP.1 (odd_natCard_inf hN L))

theorem twoGroup_map (hN : Odd (Nat.card N)) {L : Subgroup G}
    (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)) :
    IsPGroup 2 (↥(L.map (QuotientGroup.mk' N)) ⧸
      classicalInvolutionOddCore ↥(L.map (QuotientGroup.mk' N))) := by
  intro gb
  obtain ⟨xb, rfl⟩ := QuotientGroup.mk_surjective gb
  obtain ⟨l, hl, hlx⟩ := xb.2
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk (⟨l, hl⟩ : ↥L))
  refine ⟨k, ?_⟩
  have h1 : (⟨l, hl⟩ : ↥L) ^ 2 ^ k ∈ classicalInvolutionOddCore ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  have h2' : l ^ 2 ^ k ∈ oddCoreOf L :=
    mem_oddCoreOf_iff.mpr ⟨L.pow_mem hl _, by simpa using h1⟩
  have h3 : QuotientGroup.mk' N (l ^ 2 ^ k) ∈ oddCoreOf (L.map (QuotientGroup.mk' N)) := by
    rw [oddCoreOf_map_mk_of_odd (odd_natCard_inf hN L)]
    exact Subgroup.mem_map_of_mem _ h2'
  obtain ⟨hmem, h4⟩ := mem_oddCoreOf_iff.mp h3
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have e : xb ^ 2 ^ k = ⟨QuotientGroup.mk' N (l ^ 2 ^ k), hmem⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hlx]
    exact (map_pow (QuotientGroup.mk' N) l (2 ^ k)).symm
  rw [e]
  exact h4

end Members

section Image

variable {r : ℕ} {Λ : Set (Subgroup G)}

theorem TypeRFam.quot_omega4 (h : TypeRFam r Λ) (hN : Odd (Nat.card N)) :
    ∀ K ∈ quotFamily Λ N, ∀ J ∈ quotFamily Λ N, K ≠ J →
      padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J) := by
  rintro _ ⟨L, hL, rfl⟩ _ ⟨M, hM, rfl⟩ hne
  try dsimp only at *
  obtain ⟨ν, hν, hdvd⟩ := exists_conj_pow_dvd_inf hN L M
  set M' : Subgroup G := conjSub ν M with hM'def
  have hM' : M' ∈ Λ := h.hyp.conjInvariant ν M hM
  have hνmk : QuotientGroup.mk' N ν = 1 := (QuotientGroup.eq_one_iff _).mpr hν
  have himg : M'.map (QuotientGroup.mk' N) = M.map (QuotientGroup.mk' N) := by
    rw [hM'def, AscQuot.map_conjSub, hνmk, conjSub_one]
  have hLM : L ≠ M' := fun e => hne (by rw [e, himg])
  obtain ⟨h1, h2⟩ := h.hyp.omega4 L hL M' hM' hLM
  have hpos : Nat.card ↥(L ⊓ M') ≠ 0 := Nat.card_pos.ne'
  have hle : (Nat.card ↥(L.map (QuotientGroup.mk' N) ⊓ M.map (QuotientGroup.mk' N))).factorization
      2 ≤ (Nat.card ↥(L ⊓ M')).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp hdvd
  rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two] at hle
  refine ⟨hle.trans h1, fun hv => ?_⟩
  have hv' : padicValNat 2 (Nat.card ↥(L ⊓ M')) = 1 := le_antisymm h1 (hv ▸ hle)
  have hc := h2 hv'
  rw [← himg, ← Subgroup.map_commutator, oddCoreOf_map_mk_of_odd (odd_natCard_inf hN L),
    oddCoreOf_map_mk_of_odd (odd_natCard_inf hN M')]
  exact (Subgroup.map_mono hc).trans (Subgroup.map_inf_le _ _ _)

theorem TypeRFam.quotFamily (h : TypeRFam r Λ) (hN : Odd (Nat.card N)) :
    TypeRFam r (quotFamily Λ N) where
  hyp :=
    { conjInvariant := by
        rintro gb _ ⟨L, hL, rfl⟩
        try dsimp only at *
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
        exact ⟨conjSub g L, h.hyp.conjInvariant g L hL, AscQuot.map_conjSub _ g L⟩
      omega1 := by
        rintro _ ⟨L, hL, rfl⟩
        try dsimp only at *
        obtain ⟨⟨z, hz⟩, P, hP, hPnc⟩ := h.hyp.omega1 L hL
        refine ⟨⟨_, isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) hz⟩,
          P.map (QuotientGroup.mk' N), isSylow2In_map_mk hN hP, fun hc => hPnc ?_⟩
        let e := sylowMapEquiv hN hP
        exact ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _)⟩⟩
      omega2 := by
        rintro _ ⟨L, hL, rfl⟩
        try dsimp only at *
        left
        apply le_antisymm
        · rw [Subgroup.closure_le]
          intro x hx
          exact hx.1
        · conv_lhs => rw [← h.closure_twoElts hL]
          rw [MonoidHom.map_closure, Subgroup.closure_le]
          rintro _ ⟨x, ⟨hxL, hx2⟩, rfl⟩
          refine Subgroup.subset_closure ⟨⟨x, hxL, rfl⟩, ?_⟩
          rw [← MonoidHom.map_zpowers]
          exact hx2.map _
      omega3 := by
        rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ Pb Qb hPb hQb
        try dsimp only at *
        obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := K) (IsPGroup.of_bot (p := 2)) bot_le
        obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge (P := J) (IsPGroup.of_bot (p := 2)) bot_le
        rw [← natCard_sylow_map_eq hN hP hPb, ← natCard_sylow_map_eq hN hQ hQb]
        exact h.hyp.omega3 K hK J hJ P Q hP hQ
      omega4 := h.quot_omega4 hN
      omega5 := by
        rintro _ ⟨L, hL, rfl⟩ _ ⟨M, hM, rfl⟩ - zb hzb vb hvb - hv2 hvz
        try dsimp only at *
        obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
        have hzz : QuotientGroup.mk' N z = zb :=
          (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) hz).eq hzb
        obtain ⟨v, -, rfl, -⟩ := exists_isPGroup_lift_of_mem_map hvb hv2
        rw [← hzz] at hvz
        exact h.mk_mem_normalizer hN hL hz hvz }
  cls :=
    { subnormal := by
        rintro _ ⟨L, hL, rfl⟩
        try dsimp only at *
        obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
        have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) hz
        refine ⟨QuotientGroup.mk' N z, hz'.mem,
          orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one, ?_⟩
        have hle : L.map (QuotientGroup.mk' N) ≤
            Subgroup.centralizer ({QuotientGroup.mk' N z} : Set (G ⧸ N)) := by
          rintro _ ⟨x, hx, rfl⟩
          have hxz := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hL hz hx)
          rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hxz, map_mul]
        have hn : ((L.map (QuotientGroup.mk' N)).subgroupOf
            (Subgroup.centralizer ({QuotientGroup.mk' N z} : Set (G ⧸ N)))).Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
          intro gb hgb
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
          exact h.mk_mem_normalizer hN hL hz (Subgroup.mem_centralizer_singleton_iff.mp hgb)
        exact IsSubnormal.step hle hn (IsSubnormal.refl _)
      commOdd := by
        rintro _ ⟨L, hL, rfl⟩ u a b hu hu2 huu ha hb hau hbu
        try dsimp only at *
        obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := L) (IsPGroup.of_bot (p := 2)) bot_le
        obtain ⟨e⟩ := h.quat L hL P hP
        have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
        exact commOdd_of_quat (twoGroup_map hN (h.twoGroup L hL)) (isSylow2In_map_mk hN hP)
          ((sylowMapEquiv hN hP).symm.trans e) hu hu2 huu ha hb hau hbu }
  twoGroup := by
    rintro _ ⟨L, hL, rfl⟩
    try dsimp only at *
    exact twoGroup_map hN (h.twoGroup L hL)
  quat := by
    rintro _ ⟨L, hL, rfl⟩ Pb' hPb'
    try dsimp only at *
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := L) (IsPGroup.of_bot (p := 2)) bot_le
    obtain ⟨e⟩ := h.quat L hL P hP
    obtain ⟨gb, -, hconj⟩ := Thompson.exists_conj_of_isSylow2In (isSylow2In_map_mk hN hP) hPb'
    subst hconj
    exact ⟨(((P.map (QuotientGroup.mk' N)).equivMapOfInjective (MulAut.conj gb).toMonoidHom
      (MulAut.conj gb).injective).symm.trans (sylowMapEquiv hN hP).symm).trans e⟩
  tight := by
    rintro _ ⟨L, hL, rfl⟩ wb hwb gb hgb
    try dsimp only at *
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
    have hzz : QuotientGroup.mk' N z = wb :=
      (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) hz).eq hwb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzz] at hgb
    exact h.mk_mem_normalizer hN hL hz hgb
  noTwins := by
    rintro _ ⟨L, hL, rfl⟩ _ ⟨⟨M, hM, rfl⟩, wb, hwbL, hwbM⟩
    try dsimp only at *
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
    obtain ⟨y, hy⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hM
    have e1 : QuotientGroup.mk' N z = wb :=
      (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN L) hz).eq hwbL
    have e2 : QuotientGroup.mk' N y = wb :=
      (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN M) hy).eq hwbM
    obtain ⟨ν, hν, hνy⟩ := exists_conj_eq_of_map_eq hN hz.sq hy.sq (e1.trans e2.symm)
    have hMν : conjSub ν M ∈ twinSet Λ L :=
      ⟨h.hyp.conjInvariant ν M hM, z, hz, hνy ▸ hy.conj ν⟩
    have hEq := h.noTwins L hL _ hMν
    have hνmk : QuotientGroup.mk' N ν = 1 := (QuotientGroup.eq_one_iff _).mpr hν
    rw [← hEq, AscQuot.map_conjSub, hνmk, conjSub_one]

end Image

end CFSG.ClassicalInvolution.Q3.TL4
