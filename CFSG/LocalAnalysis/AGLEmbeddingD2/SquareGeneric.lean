module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRankEngine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviTransfer
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.AGLEmbeddingD2.SquareGeneric

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

local notation "A₅" => alternatingGroup (Fin 5)

theorem BorelQuotient.exists_conj_parab [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    (T : Sylow 2 Y) {J : Subgroup Y}
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) :
    ∃ π' : K →* Y, BorelQuotient D n H π' M ∧ π'.ker = π.ker ∧ borel D H ≤ J.comap π' := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  refine ⟨π', hQ, hker, fun b hb => ?_⟩
  rw [Subgroup.mem_comap]
  exact hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)

theorem hasSubquotient_leviM_of_parab (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : borel D H ≤ J.comap π) (hQ : LeviSection.HasSubquotient J (A₅ × A₅)) :
    LeviSection.HasSubquotient (leviM D (negIndices D (J.comap π))) (A₅ × A₅) := by
  have hA : LeviSection.HasSubquotient (J.comap π) (A₅ × A₅) := by
    refine LeviSection.HasSubquotient.of_map π ?_
    rwa [Subgroup.map_comap_eq_self_of_surjective h.surj]
  exact hasSubquotient_leviM h.ct h.extras hBJ h.pGroup LeviSection.commutator_alt_five_sq
    LeviSection.eq_bot_of_normal_isPGroup_two hA

section Lift

variable {X : Type*} [Group X] [Finite X] [Finite Y] {ρ : X →* Y}

omit [Finite X] [Finite Y] in
theorem eq_one_of_mem_ker_of_isPGroup (hker : Nat.Coprime 3 (Nat.card ρ.ker)) {U : Subgroup X}
    (hU : IsPGroup 3 U) {x : X} (hx : x ∈ U) (h1 : ρ x = 1) : x = 1 := by
  obtain ⟨e, he⟩ := hU ⟨x, hx⟩
  exact eq_one_of_mem_of_coprime_three hker h1 (by simpa using congrArg Subtype.val he)

theorem pRank_le_pRank_comap_of_coprime (hρ : Function.Surjective ρ)
    (hker : Nat.Coprime 3 (Nat.card ρ.ker)) (J : Subgroup Y) :
    Open.pRank 3 J ≤ Open.pRank 3 (J.comap ρ) := by
  obtain ⟨E, hEJ, hE, hcard⟩ := exists_pRank (by norm_num : 1 < 3) J
  obtain ⟨U, hUE, hU, hUm⟩ :=
    exists_isPGroup_three_map_eq hρ (isPGroup_three_of_isElemAbelian_three hE)
  have hUJ : U ≤ J.comap ρ := hUE.trans (Subgroup.comap_mono hEJ)
  have hinj : ∀ x ∈ U, ρ x = 1 → x = 1 := fun x hx h1 =>
    eq_one_of_mem_ker_of_isPGroup hker hU hx h1
  have hU1 : IsElemAbelian 3 (U.map ρ) := hUm ▸ hE
  have hUe : IsElemAbelian 3 U := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hc := hU1.1.is_comm.comm ⟨ρ a, a, a.2, rfl⟩ ⟨ρ b, b, b.2, rfl⟩
      have hc' : ρ ((a : X) * (b : X) * ((b : X) * (a : X))⁻¹) = 1 := by
        have := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at this
        rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
      have := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) hc'
      simpa using mul_inv_eq_one.1 this
    · exact hinj _ (pow_mem hx 3) (by rw [map_pow]; exact hU1.2 _ ⟨x, hx, rfl⟩)
  have hinj' : Function.Injective (ρ.comp U.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (Subtype.ext (hinj _ x.2 hx))
  have hcU : Nat.card U = 3 ^ Open.pRank 3 J := by
    have e := Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at e
    rw [e, hUm, hcard]
  exact le_pRank (by norm_num) hUJ hUe hcU

end Lift

section Torus

variable [Finite Y]

theorem three_le_pRank_of_torus (hext : SteinbergExtras D n H)
    (hπ3 : Nat.Coprime 3 (Nat.card π.ker)) {J : Subgroup Y} (hBJ : borel D H ≤ J.comap π)
    {a b c : Fin D.rank} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {x y z : K}
    (hxH : x ∈ H a) (hyH : y ∈ H b) (hzH : z ∈ H c) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hz1 : z ≠ 1) : 3 ≤ Open.pRank 3 J := by
  have hT : ∀ k, H k ≤ J.comap π := fun k => (le_iSup H k).trans (le_sup_left.trans hBJ)
  have cxy := hext.torus_commute a b x hxH y hyH
  have cxz := hext.torus_commute a c x hxH z hzH
  have cyz := hext.torus_commute b c y hyH z hzH
  have hk : ∀ w : K, w ^ 3 = 1 → π w = 1 → w = 1 := fun w hw h1 =>
    eq_one_of_mem_of_coprime_three hπ3 (show w ∈ π.ker from h1) (e := 1) (by simpa using hw)
  have hind := hext.torus_iSupIndep
  have hdisj : ∀ {k : Fin D.rank} {S : Set (Fin D.rank)}, k ∉ S →
      Disjoint (H k) (⨆ j ∈ S, H j) := fun {k S} hkS =>
    (hind k).mono_right (iSup₂_le fun j hj => le_iSup_of_le j (le_iSup_of_le
      (fun h : j = k => hkS (h ▸ hj)) le_rfl))
  set x' : ↥J := ⟨π x, hT a hxH⟩
  set y' : ↥J := ⟨π y, hT b hyH⟩
  set z' : ↥J := ⟨π z, hT c hzH⟩
  refine (three_le_pRank_of_gens (G := ↥J) (p := 3) (x := x') (y := y') (z := z')
    (Subtype.ext (by simp [x', ← map_pow, hx3])) (Subtype.ext (by simp [y', ← map_pow, hy3]))
    (Subtype.ext (by simp [z', ← map_pow, hz3])) (Subtype.ext (by simp [x', y', ← map_mul,
      cxy.eq])) (Subtype.ext (by simp [x', z', ← map_mul, cxz.eq]))
    (Subtype.ext (by simp [y', z', ← map_mul, cyz.eq])) ?_ ?_ ?_).trans
    (RealThreeRank.pRank_top_subtype_le 3 (by norm_num) J)
  · intro h1
    exact hx1 (hk x hx3 (congrArg Subtype.val h1))
  · intro e he
    have he' : π x ^ e = π y := by
      have := congrArg Subtype.val he
      simpa [x', y'] using this
    have hw : π (y * (x ^ e)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, he', mul_inv_cancel]
    have hw3 : (y * (x ^ e)⁻¹) ^ 3 = 1 := by
      rw [(cxy.symm.pow_right e).inv_right.mul_pow, hy3, inv_pow, ← pow_mul, mul_comm,
        pow_mul, hx3, one_pow, inv_one, one_mul]
    have hyx : y = x ^ e := mul_inv_eq_one.1 (hk _ hw3 hw)
    have hmem : y ∈ H b ⊓ ⨆ j ∈ ({a} : Set (Fin D.rank)), H j :=
      ⟨hyH, hyx ▸ (le_iSup₂_of_le (f := fun j (_ : j ∈ ({a} : Set (Fin D.rank))) => H j) a
        rfl le_rfl) (pow_mem hxH e)⟩
    rw [(hdisj (by simpa using hab.symm)).eq_bot] at hmem
    exact hy1 hmem
  · intro e f he
    have he' : π x ^ e * π y ^ f = π z := by
      have := congrArg Subtype.val he
      simpa [x', y', z'] using this
    have hw : π (z * (x ^ e * y ^ f)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_pow, map_pow, he', mul_inv_cancel]
    have cz : Commute z (x ^ e * y ^ f) :=
      ((cxz.symm.pow_right e).mul_right (cyz.symm.pow_right f))
    have hxy3 : (x ^ e * y ^ f) ^ 3 = 1 := by
      rw [(cxy.pow_pow e f).mul_pow, ← pow_mul, ← pow_mul, mul_comm e, mul_comm f, pow_mul,
        pow_mul, hx3, hy3, one_pow, one_pow, one_mul]
    have hw3 : (z * (x ^ e * y ^ f)⁻¹) ^ 3 = 1 := by
      rw [cz.inv_right.mul_pow, hz3, inv_pow, hxy3, inv_one, one_mul]
    have hzxy : z = x ^ e * y ^ f := mul_inv_eq_one.1 (hk _ hw3 hw)
    have hmem : z ∈ H c ⊓ ⨆ j ∈ ({a, b} : Set (Fin D.rank)), H j := by
      refine ⟨hzH, hzxy ▸ mul_mem ?_ ?_⟩
      · exact (le_iSup₂_of_le (f := fun j (_ : j ∈ ({a, b} : Set (Fin D.rank))) => H j) a
          (by simp) le_rfl) (pow_mem hxH e)
      · exact (le_iSup₂_of_le (f := fun j (_ : j ∈ ({a, b} : Set (Fin D.rank))) => H j) b
          (by simp) le_rfl) (pow_mem hyH f)
    rw [(hdisj (by simp [hac.symm, hbc.symm])).eq_bot] at hmem
    exact hz1 hmem

end Torus

section RankOne

theorem leviM_empty : leviM D ∅ = ⊥ := by
  simp [leviM]

theorem leviM_singleton (i : Fin D.rank) : leviM D {i} = rankOne D.rootGroup i := by
  simp [leviM]

theorem false_of_hasSubquotient_of_isCyclic [Finite K] {L : Subgroup K}
    (hcyc : ∀ P : Subgroup K, P ≤ L → IsPGroup 3 P → IsCyclic P)
    (h : LeviSection.HasSubquotient L (A₅ × A₅)) : False :=
  h.false_of_isCyclic hcyc LeviSection.exists_not_isCyclic_three

theorem false_of_hasSubquotient_bot [Finite K]
    (h : LeviSection.HasSubquotient (⊥ : Subgroup K) (A₅ × A₅)) : False :=
  false_of_hasSubquotient_of_isCyclic (fun P hP _ => by
    rw [le_bot_iff.1 hP]
    infer_instance) h

end RankOne

end CFSG.AGLEmbeddingD2.SquareGeneric
