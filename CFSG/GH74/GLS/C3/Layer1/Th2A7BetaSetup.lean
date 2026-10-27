module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlphaSetup

public section

namespace CFSG.GH74.GLS.Th2.AlphaStep

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a Equiv Equiv.Perm CFSG.LieType.SteinbergBR.SmallAlt
  CFSG.GH74.GLS.Th2.P43f
open scoped commutatorElement

theorem exists_even_conj_a7P_one : ∀ i : Fin 8, a7P i * a7P i = 1 → a7P i ≠ 1 →
    ∃ g : Perm (Fin 7), sign g = 1 ∧ g * a7P i * g⁻¹ = a7P 1 := by
  intro i
  fin_cases i
  · intro _ h; exact absurd (by decide) h
  · intro _ _; exact ⟨1, by decide, by decide⟩
  · intro _ _; exact ⟨swap 2 3 * swap 5 6, by decide, by decide⟩
  · intro _ _; exact ⟨swap 3 4 * swap 5 6, by decide, by decide⟩
  · intro h _; exact absurd h (by decide)
  · intro h _; exact absurd h (by decide)
  · intro _ _; exact ⟨swap 2 5 * swap 4 6, by decide, by decide⟩
  · intro _ _; exact ⟨swap 1 2 * swap 1 5 * (swap 3 4 * swap 3 6), by decide, by decide⟩

theorem perm_eq_one_of_comm_alt7 (σ : Perm (Fin 7))
    (h : ∀ a ∈ alternatingGroup (Fin 7), σ * a = a * σ) : σ = 1 := by
  apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)).1
  rw [map_one]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [MulAut.conjNormal_apply, h a a.2]
  simp

theorem exists_setup_of_witness {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G}
    {K T S : Subgroup G} (hs : Th2Std x y K T S) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    {T' S' : Subgroup G} {a : G} (hw : IsExcA7Witness x K T' S' a) :
    ∃ (z : G) (psi : G → Perm (Fin 7)), AlphaSetup x K T' a z psi ∧
      ∃ (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) (cP : Perm (Fin 7)),
        ∀ (g : G) (hg : g ∈ centralizer ({x} : Set G)),
          psi g = cP⁻¹ * C3.Layer1.Thm1.psiEquiv e7 (C3.Layer1.Back.actHom hKN ⟨g, hg⟩) * cP := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT'C, hT'N, -, hSsyl, hTS, -, -, -, ha2, hSeq, hdisj, hcomm, hTeq, ⟨eP⟩, ⟨eQ⟩⟩ := hw
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hT2 : IsPGroup 2 ↥T' := hT'C.isPGroup
  have hTC : T' ≤ centralizer ({x} : Set G) := hT'C.le
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) :=
    two_le_pRank_of_isD8 (isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P e7)
  have hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K :=
    hs.K_normal (by rw [hG.pRank_eq_four]) hcen hP2
  have hP' : IsSylowOf 2 (T' ⊓ K) K := by
    have h1 := hT'N.inf_of_le_normalizer hs.K_le_NxK (fun n hn => hn.2)
    rwa [inf_assoc, inf_eq_right.2 hs.K_le_NxK] at h1
  obtain ⟨ψ, hker, hψK⟩ := lemma113d_alt hs.K_le_C hKN (n := 7) (by norm_num) (by norm_num) e7
  have hker' : ψ.ker =
      (CMK (centralizer ({x} : Set G)) K).subgroupOf (centralizer ({x} : Set G)) := hker
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt7 hT2 hP' e7
  obtain ⟨c, hc1, hc2⟩ := exists_conj_model (X := ι.range) hιcard
  obtain ⟨cP, hcP⟩ : ∃ cP : Perm (Fin 7), cP = (c : Perm (Fin 7)) := ⟨_, rfl⟩
  let psi : G → Perm (Fin 7) := fun g =>
    if hg : g ∈ centralizer ({x} : Set G) then cP⁻¹ * (ψ ⟨g, hg⟩ : Perm (Fin 7)) * cP else 1
  have hpsiC : ∀ g (hg : g ∈ centralizer ({x} : Set G)),
      psi g = cP⁻¹ * (ψ ⟨g, hg⟩ : Perm (Fin 7)) * cP := fun g hg => by
    simp only [psi, hg, dite_true]
  have hpsimul : ∀ g ∈ centralizer ({x} : Set G), ∀ h ∈ centralizer ({x} : Set G),
      psi (g * h) = psi g * psi h := by
    intro g hg h hh
    rw [hpsiC _ ((centralizer ({x} : Set G)).mul_mem hg hh), hpsiC g hg, hpsiC h hh]
    have : ψ ⟨g * h, (centralizer ({x} : Set G)).mul_mem hg hh⟩ = ψ ⟨g, hg⟩ * ψ ⟨h, hh⟩ :=
      map_mul ψ ⟨g, hg⟩ ⟨h, hh⟩
    rw [this]
    group
  have hconjone : ∀ u : Perm (Fin 7), cP⁻¹ * u * cP = 1 ↔ u = 1 := by
    intro u
    constructor
    · intro h
      calc u = cP * (cP⁻¹ * u * cP) * cP⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hpsiker : ∀ g ∈ centralizer ({x} : Set G), psi g = 1 ↔ g ∈ CxK x K := by
    intro g hg
    rw [hpsiC g hg, hconjone, ← MonoidHom.mem_ker, hker', Subgroup.mem_subgroupOf]
    rfl
  have hpsiKker : ∀ k ∈ K, psi k = 1 ↔ k ∈ pPrimeCoreOf 2 K := by
    intro k hk
    have hkC : k ∈ centralizer ({x} : Set G) := hs.K_le_C hk
    rw [hpsiC k hkC, hconjone, hψK k hk]
    constructor
    · intro h
      have h2' : e7 (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 := Subtype.ext h
      have h2 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 :=
        e7.injective (h2'.trans (map_one e7).symm)
      exact Setup91.mem_pPrimeCoreOf_iff.2 ⟨hk, (QuotientGroup.eq_one_iff _).1 h2⟩
    · intro h
      obtain ⟨hk', h2⟩ := Setup91.mem_pPrimeCoreOf_iff.1 h
      have h3 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 := (QuotientGroup.eq_one_iff _).2 h2
      rw [h3, map_one]
      rfl
  have hpsisurj : ∀ h : Perm (Fin 7), sign h = 1 → ∃ k ∈ K, psi k = h := by
    intro h hh
    have hh' : cP * h * cP⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [mem_alternatingGroup, map_mul, map_mul, hh, map_inv]
      have : sign cP = 1 := by rw [hcP]; exact mem_alternatingGroup.1 c.2
      rw [this]
      simp
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e7.symm ⟨cP * h * cP⁻¹, hh'⟩)
    refine ⟨(q : G), q.2, ?_⟩
    have hqC : (q : G) ∈ centralizer ({x} : Set G) := hs.K_le_C q.2
    rw [hpsiC _ hqC]
    have h1 : ψ ⟨(q : G), hqC⟩ =
        ((e7 (QuotientGroup.mk q) : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
      hψK (q : G) q.2
    rw [h1, hq, MulEquiv.apply_symm_apply]
    simp only
    group
  have hιψ : ∀ p : ↥(T' ⊓ K), ((ι p : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ψ ⟨(p : G), hTC p.2.1⟩ := by
    intro p
    rw [hι p]
    exact (hψK p p.2.2).symm
  have hpsiP : ∀ u ∈ T' ⊓ K, ∃ i : Fin 8, psi u = a7P i := by
    intro u hu
    have hmem : ι ⟨u, hu⟩ ∈ ι.range := ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨i, hi⟩ := hc2 _ hmem
    refine ⟨i, ?_⟩
    rw [hpsiC u (hTC hu.1), ← hιψ ⟨u, hu⟩]
    have hi' : a7P i = cP⁻¹ * ((ι ⟨u, hu⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) * cP := by
      rw [hcP]
      simpa using hi
    exact hi'.symm
  have hpsiPsurj : ∀ i : Fin 8, ∃ u ∈ T' ⊓ K, psi u = a7P i := by
    intro i
    have hy : (⟨a7P i, mem_alternatingGroup.2 (a7P_sign i)⟩ : alternatingGroup (Fin 7)) ∈
        CFSG.LieType.SteinbergBR.SmallAlt.finSubgroup a7P a7P_mul a7P_inv a7P_one := ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := hc1 _ hy
    refine ⟨(p : G), p.2, ?_⟩
    rw [hpsiC _ (hTC p.2.1), ← hιψ p, hp]
    have hp' : (((c * ⟨a7P i, mem_alternatingGroup.2 (a7P_sign i)⟩ * c⁻¹ :
        alternatingGroup (Fin 7)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        cP * a7P i * cP⁻¹ := by
      rw [hcP]
      simp
    rw [hp']
    group
  have hYodd : ∀ y ∈ pPrimeCoreOf 2 K, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hy)
  have hPsiD : PsiData (centralizer ({x} : Set G)) K psi :=
    { K_le := hs.K_le_C
      K_norm := hKN
      mul := hpsimul
      ker_odd := fun k hk h => hYodd k ((hpsiKker k hk).1 h)
      surj := hpsisurj }
  have hPinv : ∀ u ∈ T' ⊓ K, psi u * psi u = 1 → u * u = 1 := by
    intro u hu h
    have huC : u ∈ centralizer ({x} : Set G) := hTC hu.1
    have h1 : psi (u * u) = 1 := by rw [hpsimul u huC u huC]; exact h
    have hmemK : u * u ∈ K := K.mul_mem hu.2 hu.2
    have hodd : Odd (orderOf (u * u)) := hPsiD.ker_odd _ hmemK h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT2) (⟨u * u, T'.mul_mem hu.1 hu.1⟩ : ↥T')
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      have : Even (2 ^ k) := Nat.even_pow.2 ⟨even_two, hk0⟩
      rw [← hk] at this
      exact (Nat.not_even_iff_odd.2 hodd) this
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hs.orderOf_x, sq] at h
    exact h
  have hx1 : x ≠ 1 := by
    intro h
    have := hs.orderOf_x
    rw [h, orderOf_one] at this
    omega
  have hxT' : x ∈ T' :=
    C3.Layer1.Back.mem_of_isSylowOf_of_central hT'C (mem_centralizer_singleton_iff.2 rfl)
      (fun _ hs' => mem_centralizer_singleton_iff.1 hs') hs.orderOf_x
  have hxQ : x ∈ T' ⊓ CxK x K := ⟨hxT', hs.x_mem_CxK⟩
  have hPD8 : IsD8 (T' ⊓ K) := ⟨eP⟩
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu, hzsq⟩ := hPD8.exists_central_sq
  have hQinv : ∀ u ∈ T' ⊓ CxK x K, u * u = 1 → u = 1 ∨ u = x := by
    intro u hu huu
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · right
      have hmodel : ∀ v w : Multiplicative (ZMod 4), v * v = 1 → w * w = 1 → v ≠ 1 → w ≠ 1 →
          v = w := by decide
      have h1 : eQ ⟨u, hu⟩ * eQ ⟨u, hu⟩ = 1 := by
        rw [← map_mul]
        have : (⟨u, hu⟩ : ↥(T' ⊓ CxK x K)) * ⟨u, hu⟩ = 1 := Subtype.ext huu
        rw [this, map_one]
      have h2 : eQ ⟨x, hxQ⟩ * eQ ⟨x, hxQ⟩ = 1 := by
        rw [← map_mul]
        have : (⟨x, hxQ⟩ : ↥(T' ⊓ CxK x K)) * ⟨x, hxQ⟩ = 1 := Subtype.ext hxx
        rw [this, map_one]
      have h3 : eQ ⟨u, hu⟩ ≠ 1 := by
        intro h
        exact hu1 (congrArg Subtype.val (eQ.injective (h.trans (map_one eQ).symm)))
      have h4 : eQ ⟨x, hxQ⟩ ≠ 1 := by
        intro h
        exact hx1 (congrArg Subtype.val (eQ.injective (h.trans (map_one eQ).symm)))
      exact congrArg Subtype.val (eQ.injective (hmodel _ _ h1 h2 h3 h4))
  have hzT : ∀ t ∈ T', z * t = t * z := by
    intro t ht
    have ht' : t ∈ (T' ⊓ K) ⊔ (T' ⊓ K).map (MulAut.conj a).toMonoidHom := by
      rw [← hTeq]; exact ht
    obtain ⟨u, hu, u', hu', rfl⟩ := mem_sup_of_commute hcomm ht'
    have h1 : u * z = z * u := hzc u hu
    have h2 : z * u' = u' * z := hcomm z hzP u' hu'
    calc z * (u * u') = (z * u) * u' := by group
      _ = (u * z) * u' := by rw [h1]
      _ = u * (z * u') := by group
      _ = u * (u' * z) := by rw [h2]
      _ = (u * u') * z := by group
  have haa : a * a ∈ T' := by simpa [sq] using ha2
  have hxTc : ∀ t ∈ T', x * t = t * x := fun t ht =>
    (mem_centralizer_singleton_iff.1 (hTC ht)).symm
  have hxsup : x ∈ (T' ⊓ K) ⊔ (T' ⊓ K).map (MulAut.conj a).toMonoidHom := by
    rw [← hTeq]; exact hxT'
  obtain ⟨u, hu, u', hu', hxuu⟩ := mem_sup_of_commute hcomm hxsup
  have hPaT0 : (T' ⊓ K).map (MulAut.conj a).toMonoidHom ≤ T' := by
    intro f hf
    have : f ∈ (T' ⊓ K) ⊔ (T' ⊓ K).map (MulAut.conj a).toMonoidHom := Subgroup.mem_sup_right hf
    rwa [← hTeq] at this
  have hucen : ∀ p ∈ T' ⊓ K, p * u = u * p := by
    intro p hp
    have h1 : x * p = p * x := hxTc p hp.1
    have h2 : p * u' = u' * p := hcomm p hp u' hu'
    rw [hxuu] at h1
    have h3 : u * p * u' = p * u * u' := by
      calc u * p * u' = u * (p * u') := by group
        _ = u * (u' * p) := by rw [h2]
        _ = u * u' * p := by group
        _ = p * (u * u') := h1
        _ = p * u * u' := by group
    exact (mul_right_cancel h3).symm
  obtain ⟨p', hp', hp'u'⟩ := Subgroup.mem_map.1 hu'
  have hu'eq : u' = a * p' * a⁻¹ := by rw [← hp'u']; simp [MulAut.conj_apply]
  have hp'cen : ∀ p ∈ T' ⊓ K, p * p' = p' * p := by
    intro p hp
    have hpa : a * p * a⁻¹ ∈ (T' ⊓ K).map (MulAut.conj a).toMonoidHom :=
      Subgroup.mem_map.2 ⟨p, hp, by simp [MulAut.conj_apply]⟩
    have h1 : x * (a * p * a⁻¹) = (a * p * a⁻¹) * x := hxTc _ (hPaT0 hpa)
    have h2 : u * (a * p * a⁻¹) = (a * p * a⁻¹) * u := hcomm u hu _ hpa
    rw [hxuu] at h1
    have h3 : u' * (a * p * a⁻¹) = (a * p * a⁻¹) * u' := by
      have h4 : u * (u' * (a * p * a⁻¹)) = u * ((a * p * a⁻¹) * u') := by
        calc u * (u' * (a * p * a⁻¹)) = u * u' * (a * p * a⁻¹) := by group
          _ = (a * p * a⁻¹) * (u * u') := h1
          _ = ((a * p * a⁻¹) * u) * u' := by group
          _ = (u * (a * p * a⁻¹)) * u' := by rw [h2]
          _ = u * ((a * p * a⁻¹) * u') := by group
      exact mul_left_cancel h4
    rw [hu'eq] at h3
    have h5 : a * (p' * p) * a⁻¹ = a * (p * p') * a⁻¹ := by
      calc a * (p' * p) * a⁻¹ = a * p' * a⁻¹ * (a * p * a⁻¹) := by group
        _ = a * p * a⁻¹ * (a * p' * a⁻¹) := h3
        _ = a * (p * p') * a⁻¹ := by group
    have h6 : p' * p = p * p' := by
      have := congrArg (fun t => a⁻¹ * t * a) h5
      simpa [mul_assoc] using this
    exact h6.symm
  have hcenP : ∀ w ∈ T' ⊓ K, (∀ p ∈ T' ⊓ K, p * w = w * p) → w = 1 ∨ w = z := hzu
  have hzPa : a * z * a⁻¹ ∈ (T' ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.2 ⟨z, hzP, by simp [MulAut.conj_apply]⟩
  have hxz : a * z * a⁻¹ = x := by
    rcases hcenP u hu hucen with hu1 | huz <;> rcases hcenP p' hp' hp'cen with hp1 | hpz
    · exfalso
      apply hx1
      rw [hxuu, hu1, hu'eq, hp1]
      group
    · rw [hxuu, hu1, hu'eq, hpz]
      group
    · exfalso
      have hxz' : x = z := by rw [hxuu, huz, hu'eq, hp1]; group
      have hxK : x ∈ K := hxz' ▸ hzP.2
      have hxY : x ∈ pPrimeCoreOf 2 K :=
        (hpsiKker x hxK).1 ((hpsiker x (hTC hxT')).2 hs.x_mem_CxK)
      have hodd := hYodd x hxY
      rw [hs.orderOf_x] at hodd
      exact absurd hodd (by decide)
    · exfalso
      have hxe : x = z * (a * z * a⁻¹) := by rw [hxuu, huz, hu'eq, hpz]
      have hzc' : z * (a * z * a⁻¹) = (a * z * a⁻¹) * z := hcomm z hzP _ hzPa
      have hax : a * x * a⁻¹ = x := by
        have h1 : (a * a) * z * (a * a)⁻¹ = z := by
          have := hzT (a * a) haa
          calc (a * a) * z * (a * a)⁻¹ = z * (a * a) * (a * a)⁻¹ := by rw [this]
            _ = z := by group
        calc a * x * a⁻¹ = a * (z * (a * z * a⁻¹)) * a⁻¹ := by rw [hxe]
          _ = (a * z * a⁻¹) * ((a * a) * z * (a * a)⁻¹) := by group
          _ = (a * z * a⁻¹) * z := by rw [h1]
          _ = z * (a * z * a⁻¹) := hzc'.symm
          _ = x := hxe.symm
      have haC : a ∈ centralizer ({x} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc a * x = (a * x * a⁻¹) * a := by group
          _ = x * a := by rw [hax]
      have hSC : S' ≤ centralizer ({x} : Set G) := by
        rw [hSeq]
        exact sup_le hTC ((Subgroup.zpowers_le).2 haC)
      have hS2 : IsPGroup 2 ↥S' := hSsyl.isPGroup
      have heq := hT'C.eq_of_le hTS.le hSC hS2
      exact (ne_of_lt hTS) heq.symm
  have hxa : a * x * a⁻¹ = z := by
    have h1 := hzT (a * a) haa
    rw [← hxz]
    calc a * (a * z * a⁻¹) * a⁻¹ = (a * a) * z * (a * a)⁻¹ := by group
      _ = z := by rw [← h1]; group
  have hPaT : (T' ⊓ K).map (MulAut.conj a).toMonoidHom ≤ T' := by
    intro f hf
    have : f ∈ (T' ⊓ K) ⊔ (T' ⊓ K).map (MulAut.conj a).toMonoidHom := Subgroup.mem_sup_right hf
    rwa [← hTeq] at this
  have hpsiz : psi z = a7P 1 := by
    obtain ⟨i, hi⟩ := hpsiP z hzP
    have hcen : ∀ j : Fin 8, a7P i * a7P j = a7P j * a7P i := by
      intro j
      obtain ⟨u, hu, hj⟩ := hpsiPsurj j
      rw [← hi, ← hj, ← hpsimul z (hTC hzP.1) u (hTC hu.1), ← hpsimul u (hTC hu.1) z (hTC hzP.1),
        hzc u hu]
    rcases a7P_central_idx i hcen with h0 | h1
    · exfalso
      have h0' : psi z = 1 := by rw [hi, h0]; rfl
      have hodd : Odd (orderOf z) := hPsiD.ker_odd z hzP.2 h0'
      have h2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
      rw [h2] at hodd
      exact absurd hodd (by decide)
    · rw [hi, h1]
  have hpsix : psi x = 1 := (hpsiker x (hTC hxT')).2 hs.x_mem_CxK
  have hψeq : ∀ g : ↥(centralizer ({x} : Set G)),
      ψ g = C3.Layer1.Thm1.psiEquiv e7 (C3.Layer1.Back.actHom hKN g) := by
    intro g
    set π := C3.Layer1.Thm1.psiEquiv e7 (C3.Layer1.Back.actHom hKN g) with hπ
    have hcomm' : ∀ b ∈ alternatingGroup (Fin 7), (π⁻¹ * ψ g) * b = b * (π⁻¹ * ψ g) := by
      intro b hb
      obtain ⟨kb, hkb⟩ := e7.surjective ⟨b, hb⟩
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective kb
      have hkC : k ∈ centralizer ({x} : Set G) := hs.K_le_C hk
      have hgk : (g : G) * k * (g : G)⁻¹ ∈ K := hKN g g.2 k hk
      have h1 : ψ ⟨(g : G) * k * (g : G)⁻¹, hs.K_le_C hgk⟩ =
          ((e7 (QuotientGroup.mk (⟨(g : G) * k * (g : G)⁻¹, hgk⟩ : ↥K)) :
            alternatingGroup (Fin 7)) :
            Perm (Fin 7)) := hψK _ hgk
      have h2 : ψ ⟨(g : G) * k * (g : G)⁻¹, hs.K_le_C hgk⟩ = ψ g * ψ ⟨k, hkC⟩ * (ψ g)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      have h3 : ψ ⟨k, hkC⟩ = ((e7 (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) : alternatingGroup (Fin 7)) :
          Perm (Fin 7)) := hψK k hk
      have h4 : ((e7 (QuotientGroup.mk (⟨(g : G) * k * (g : G)⁻¹, hgk⟩ : ↥K)) :
          alternatingGroup (Fin 7)) : Perm (Fin 7)) =
          π * ((e7 (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) : alternatingGroup (Fin 7)) :
            Perm (Fin 7)) * π⁻¹ := by
        rw [hπ, ← C3.Layer1.Thm1.psi_apply e7 (C3.Layer1.Back.actHom hKN g)]
        rw [C3.Layer1.Back.actHom_mk hKN g ⟨k, hk⟩]
      have h3' : ψ ⟨k, hkC⟩ = b := by rw [h3, hkb]
      have h5 : ψ g * b * (ψ g)⁻¹ = π * b * π⁻¹ := by
        rw [← h3', ← h2, h1, h4, h3]
      calc π⁻¹ * ψ g * b = π⁻¹ * (ψ g * b * (ψ g)⁻¹) * ψ g := by group
        _ = π⁻¹ * (π * b * π⁻¹) * ψ g := by rw [h5]
        _ = b * (π⁻¹ * ψ g) := by group
    have h1 := perm_eq_one_of_comm_alt7 _ hcomm'
    calc ψ g = π * (π⁻¹ * ψ g) := by group
      _ = π := by rw [h1, mul_one]
  refine ⟨z, psi, ?_, hKN, cP, fun g hg => by rw [hpsiC g hg, hψeq]⟩
  exact
    { psiD := hPsiD
      psi_ker := hpsiker
      psi_P := hpsiP
      psi_P_surj := hpsiPsurj
      P_inv := hPinv
      T_le_C := hTC
      x_sq := hxx
      x_ne := hx1
      x_mem_T := hxT'
      psi_x := hpsix
      z_mem := hzP
      z_ne := hz1
      z_sq := hzz
      z_central := hzT
      psi_z := hpsiz
      hxz := hxz
      hxa := hxa
      haa := haa
      Pa_le := hPaT
      comm := hcomm
      disj := hdisj
      T_eq := hTeq
      Q_invol := hQinv }


section Beta

variable {G : Type} [Group G] {x z a : G} {K T : Subgroup G} {psi : G → Perm (Fin 7)}

theorem AlphaSetup.psi_ne_z_of_sq (A : AlphaSetup x K T a z psi) {v : G}
    (hv : v ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) (hvv : v * v = 1) : psi v ≠ a7P 1 := by
  intro h
  have hvT : v ∈ T := A.Pa_le hv
  have hvC := A.T_le_C hvT
  have hzC := A.T_le_C A.z_mem.1
  have h11 : a7P 1 * a7P 1 = 1 := by decide
  have h1 : psi (v * z) = 1 := by
    rw [A.psiD.mul v hvC z hzC, h, A.psi_z, h11]
  have hvz : v * z ∈ CxK x K := (A.psi_ker _ ((centralizer ({x} : Set G)).mul_mem hvC hzC)).1 h1
  have hvzQ : v * z ∈ T ⊓ CxK x K := ⟨T.mul_mem hvT A.z_mem.1, hvz⟩
  have hzv : z * v = v * z := A.z_central v hvT
  have hvz2 : (v * z) * (v * z) = 1 := by
    calc (v * z) * (v * z) = v * (z * v) * z := by group
      _ = v * (v * z) * z := by rw [hzv]
      _ = (v * v) * (z * z) := by group
      _ = 1 := by rw [hvv, A.z_sq, one_mul]
  have hxPa : x ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.2 ⟨z, A.z_mem, by simp [MulAut.conj_apply, A.hxz]⟩
  have hzPa : z ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom := by
    rcases A.Q_invol _ hvzQ hvz2 with h0 | h0
    · have : z = v⁻¹ := by
        calc z = v⁻¹ * (v * z) := by group
          _ = v⁻¹ := by rw [h0, mul_one]
      rw [this]; exact Subgroup.inv_mem _ hv
    · have : z = v⁻¹ * x := by
        calc z = v⁻¹ * (v * z) := by group
          _ = v⁻¹ * x := by rw [h0]
      rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hxPa
  have hz1 : z ∈ (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom := ⟨A.z_mem, hzPa⟩
  rw [A.disj, Subgroup.mem_bot] at hz1
  exact A.z_ne hz1

theorem AlphaSetup.psi_refl_of_sq (A : AlphaSetup x K T a z psi) {u : G}
    (hu : u ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) (huu : u * u = 1) (hu1 : u ≠ 1)
    (hux : u ≠ x) : psi u = swap 5 6 ∨ psi u = a7P 1 * swap 5 6 := by
  have huT : u ∈ T := A.Pa_le hu
  have huC := A.T_le_C huT
  have hcomm : ∀ k : Fin 8, psi u * a7P k = a7P k * psi u := by
    intro k
    obtain ⟨w, hw, hwk⟩ := A.psi_P_surj k
    have hwC := A.T_le_C hw.1
    rw [← hwk, ← A.psiD.mul u huC w hwC, ← A.psiD.mul w hwC u huC, A.comm w hw u hu]
  rcases cent_a7P (psi u) hcomm with h | h | h | h
  · exfalso
    have hmem : u ∈ CxK x K := (A.psi_ker u huC).1 h
    rcases A.Q_invol u ⟨huT, hmem⟩ huu with h1 | h1
    · exact hu1 h1
    · exact hux h1
  · exact absurd h (A.psi_ne_z_of_sq hu huu)
  · exact Or.inl h
  · exact Or.inr h

theorem AlphaSetup.exists_refl_z_swap [Finite G] (A : AlphaSetup x K T a z psi)
    (eP : ↥(T ⊓ K) ≃* DihedralGroup 4) (eQ : ↥(T ⊓ CxK x K) ≃* Multiplicative (ZMod 4))
    (hβ : ¬ (T ⊓ CxK x K ≤ (T ⊓ K).map (MulAut.conj a).toMonoidHom)) :
    ∃ s ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom, s * s = 1 ∧ s ≠ 1 ∧ s ≠ x ∧
      psi s = a7P 1 * swap 5 6 := by
  classical
  by_contra hno
  push Not at hno
  set p₁ : G := ((eP.symm (DihedralGroup.sr 0) : ↥(T ⊓ K)) : G) with hp₁
  set p₂ : G := ((eP.symm (DihedralGroup.sr 1) : ↥(T ⊓ K)) : G) with hp₂
  have hp₁P : p₁ ∈ T ⊓ K := (eP.symm (DihedralGroup.sr 0)).2
  have hp₂P : p₂ ∈ T ⊓ K := (eP.symm (DihedralGroup.sr 1)).2
  have hzr : eP ⟨z, A.z_mem⟩ = DihedralGroup.r 2 := by
    have hcen : ∀ d : DihedralGroup 4, d * eP ⟨z, A.z_mem⟩ = eP ⟨z, A.z_mem⟩ * d := by
      intro d
      obtain ⟨q, rfl⟩ := eP.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (A.z_central q q.2.1).symm
    have hne : eP ⟨z, A.z_mem⟩ ≠ 1 := by
      intro h
      apply A.z_ne
      have := eP.injective (h.trans (map_one eP).symm)
      exact congrArg Subtype.val this
    have key : ∀ w : DihedralGroup 4, (∀ d : DihedralGroup 4, d * w = w * d) → w ≠ 1 →
        w = DihedralGroup.r 2 := by decide
    exact key _ hcen hne
  have hpz : ∀ i : ZMod 4, ((eP.symm (DihedralGroup.sr i) : ↥(T ⊓ K)) : G) ≠ z := by
    intro i h
    have h1 : eP.symm (DihedralGroup.sr i) = ⟨z, A.z_mem⟩ := Subtype.ext h
    have h2 : DihedralGroup.sr i = eP ⟨z, A.z_mem⟩ := by rw [← h1, MulEquiv.apply_symm_apply]
    rw [hzr] at h2
    have key : ∀ j : ZMod 4, DihedralGroup.sr j ≠ (DihedralGroup.r 2 : DihedralGroup 4) := by
      decide
    exact key i h2
  have hmemPa : ∀ p ∈ T ⊓ K, a * p * a⁻¹ ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    fun p hp => Subgroup.mem_map.2 ⟨p, hp, by simp [MulAut.conj_apply]⟩
  have hsr_inv : ∀ i : ZMod 4, ((eP.symm (DihedralGroup.sr i) : ↥(T ⊓ K)) : G) *
      ((eP.symm (DihedralGroup.sr i) : ↥(T ⊓ K)) : G) = 1 := by
    intro i
    have : eP.symm (DihedralGroup.sr i) * eP.symm (DihedralGroup.sr i) = 1 := by
      rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
    exact congrArg Subtype.val this
  have hsr_ne : ∀ i : ZMod 4, ((eP.symm (DihedralGroup.sr i) : ↥(T ⊓ K)) : G) ≠ 1 := by
    intro i h
    have h1 : eP.symm (DihedralGroup.sr i) = 1 := Subtype.ext h
    have h2 : DihedralGroup.sr i = 1 := by
      rw [← MulEquiv.apply_symm_apply eP (DihedralGroup.sr i), h1, map_one]
    have key : ∀ j : ZMod 4, DihedralGroup.sr j ≠ (1 : DihedralGroup 4) := by decide
    exact key i h2
  have hrefl : ∀ i : ZMod 4, psi (a * ((eP.symm (DihedralGroup.sr i) : ↥(T ⊓ K)) : G) * a⁻¹) =
      swap 5 6 := by
    intro i
    set p := ((eP.symm (DihedralGroup.sr i) : ↥(T ⊓ K)) : G)
    have hpP : p ∈ T ⊓ K := (eP.symm (DihedralGroup.sr i)).2
    have hu := hmemPa p hpP
    have huu : (a * p * a⁻¹) * (a * p * a⁻¹) = 1 := by
      calc (a * p * a⁻¹) * (a * p * a⁻¹) = a * (p * p) * a⁻¹ := by group
        _ = 1 := by rw [hsr_inv i]; group
    have hu1 : a * p * a⁻¹ ≠ 1 := by
      intro h
      apply hsr_ne i
      calc p = a⁻¹ * (a * p * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group
    have hux : a * p * a⁻¹ ≠ x := by
      intro h
      apply hpz i
      calc p = a⁻¹ * (a * p * a⁻¹) * a := by group
        _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [h, A.hxz]
        _ = z := by group
    rcases A.psi_refl_of_sq hu huu hu1 hux with h | h
    · exact h
    · exact absurd h (hno _ hu huu hu1 hux)
  set u : G := a * p₁ * a⁻¹ * (a * p₂ * a⁻¹) with hu
  have huPa : u ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mul_mem _ (hmemPa p₁ hp₁P) (hmemPa p₂ hp₂P)
  have huT : u ∈ T := A.Pa_le huPa
  have hpsiu : psi u = 1 := by
    rw [hu, A.psiD.mul _ (A.T_le_C (A.Pa_le (hmemPa p₁ hp₁P))) _
      (A.T_le_C (A.Pa_le (hmemPa p₂ hp₂P))), hrefl 0, hrefl 1]
    decide
  have huQ : u ∈ T ⊓ CxK x K := ⟨huT, (A.psi_ker u (A.T_le_C huT)).1 hpsiu⟩
  have hord : orderOf u = 4 := by
    have h1 : u = MulAut.conj a (p₁ * p₂) := by rw [hu, MulAut.conj_apply]; group
    have h2 : p₁ * p₂ = ((eP.symm (DihedralGroup.r 1) : ↥(T ⊓ K)) : G) := by
      have : eP.symm (DihedralGroup.sr 0) * eP.symm (DihedralGroup.sr 1) =
          eP.symm (DihedralGroup.r 1) := by
        rw [← map_mul, DihedralGroup.sr_mul_sr]
        norm_num
      exact congrArg Subtype.val this
    rw [h1, MulEquiv.orderOf_eq, h2, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  apply hβ
  have hQcard : Nat.card ↥(T ⊓ CxK x K) = 4 := by
    rw [Nat.card_congr eQ.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hzle : zpowers u ≤ T ⊓ CxK x K := (Subgroup.zpowers_le).2 huQ
  have heq : zpowers u = T ⊓ CxK x K := by
    apply Subgroup.eq_of_le_of_card_ge hzle
    rw [hQcard, Nat.card_zpowers, hord]
  rw [← heq]
  exact (Subgroup.zpowers_le).2 huPa

end Beta

section BetaE

variable {G : Type} [Group G] {x z a : G} {K T : Subgroup G} {psi : G → Perm (Fin 7)}

theorem mem_or_eq_mul_of_mem_sup_zpowers_sq {T : Subgroup G} {a : G}
    (haT : ∀ t ∈ T, a * t * a⁻¹ ∈ T) (haT' : ∀ t ∈ T, a⁻¹ * t * a ∈ T) (haa : a * a ∈ T)
    {j : G} (hj : j ∈ T ⊔ Subgroup.zpowers a) : j ∈ T ∨ ∃ t ∈ T, j = t * a := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ T ∨ ∃ t ∈ T, x = t * a}
      mul_mem' := by
        rintro _ _ (hx | ⟨t, ht, rfl⟩) (hy | ⟨t', ht', rfl⟩)
        · exact Or.inl (T.mul_mem hx hy)
        · exact Or.inr ⟨_ * t', T.mul_mem hx ht', by group⟩
        · refine Or.inr ⟨t * (a * _ * a⁻¹), T.mul_mem ht (haT _ hy), ?_⟩
          group
        · refine Or.inl ?_
          have : t * a * (t' * a) = t * (a * t' * a⁻¹) * (a * a) := by group
          rw [this]
          exact T.mul_mem (T.mul_mem ht (haT t' ht')) haa
      one_mem' := Or.inl T.one_mem
      inv_mem' := by
        rintro _ (hx | ⟨t, ht, rfl⟩)
        · exact Or.inl (T.inv_mem hx)
        · refine Or.inr ⟨(a⁻¹ * t⁻¹ * a) * (a * a)⁻¹, T.mul_mem (haT' _ (T.inv_mem ht))
            (T.inv_mem haa), ?_⟩
          group }
  have hle : T ⊔ Subgroup.zpowers a ≤ S :=
    sup_le (fun g hg => Or.inl hg) ((Subgroup.zpowers_le).2 (Or.inr ⟨1, T.one_mem, by group⟩))
  exact hle hj

theorem AlphaSetup.eq_one_or_eq_xz_of_central (A : AlphaSetup x K T a z psi)
    (eP : ↥(T ⊓ K) ≃* DihedralGroup 4) {S : Subgroup G} (hSeq : S = T ⊔ zpowers a)
    (haN : a ∈ normalizer (T : Set G)) :
    ∀ r ∈ S, (∀ t ∈ S, r * t = t * r) → r = 1 ∨ r = x * z := by
  intro r hr hrc
  have hxPa : x ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
    Subgroup.mem_map.2 ⟨z, A.z_mem, by simp [MulAut.conj_apply, A.hxz]⟩
  have hxz_ne : x ≠ z := by
    intro h
    have hz : z ∈ (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom := ⟨A.z_mem, h ▸ hxPa⟩
    rw [A.disj, Subgroup.mem_bot] at hz
    exact A.z_ne hz
  have hTS : T ≤ S := by rw [hSeq]; exact le_sup_left
  have haS : a ∈ S := by rw [hSeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hxc : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (mem_centralizer_singleton_iff.1 (A.T_le_C ht)).symm
  have haT : ∀ t ∈ T, a * t * a⁻¹ ∈ T := fun t ht => (Subgroup.mem_normalizer_iff.1 haN t).1 ht
  have haT' : ∀ t ∈ T, a⁻¹ * t * a ∈ T := fun t ht => by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haN) t).1 ht
    simpa using this
  have hra : a * r * a⁻¹ = r := by
    have := hrc a haS
    calc a * r * a⁻¹ = r * a * a⁻¹ := by rw [this]
      _ = r := by group
  rcases mem_or_eq_mul_of_mem_sup_zpowers_sq haT haT' A.haa (hSeq ▸ hr) with hrT | ⟨t, ht, rfl⟩
  swap
  ·
    exfalso
    apply hxz_ne
    have h1 : (t * a) * z * (t * a)⁻¹ = z := by
      have := hrc z (hTS A.z_mem.1)
      calc (t * a) * z * (t * a)⁻¹ = z * (t * a) * (t * a)⁻¹ := by rw [this]
        _ = z := by group
    have h2 : (t * a) * z * (t * a)⁻¹ = t * x * t⁻¹ := by
      rw [← A.hxz]; group
    have h3 : t * x * t⁻¹ = x := by
      rw [← hxc t ht]; group
    rw [← h3, ← h2, h1]
  ·
    have hPD8 : IsD8 (T ⊓ K) := ⟨eP⟩
    obtain ⟨z', hz'P, -, -, -, hz'u, -⟩ := hPD8.exists_central_sq
    have hzz' : z = z' := by
      rcases hz'u z A.z_mem (fun p hp => (A.z_central p hp.1).symm) with h | h
      · exact absurd h A.z_ne
      · exact h
    subst hzz'
    have hrsup : r ∈ (T ⊓ K) ⊔ (T ⊓ K).map (MulAut.conj a).toMonoidHom := by
      rw [← A.T_eq]; exact hrT
    obtain ⟨u, hu, u', hu', hruu⟩ := mem_sup_of_commute A.comm hrsup
    have hucen : ∀ p ∈ T ⊓ K, p * u = u * p := by
      intro p hp
      have h1 : r * p = p * r := hrc p (hTS hp.1)
      have h2 : p * u' = u' * p := A.comm p hp u' hu'
      rw [hruu] at h1
      have h3 : u * p * u' = p * u * u' := by
        calc u * p * u' = u * (p * u') := by group
          _ = u * (u' * p) := by rw [h2]
          _ = u * u' * p := by group
          _ = p * (u * u') := h1
          _ = p * u * u' := by group
      exact (mul_right_cancel h3).symm
    obtain ⟨p', hp', hp'u'⟩ := Subgroup.mem_map.1 hu'
    have hu'eq : u' = a * p' * a⁻¹ := by rw [← hp'u']; simp [MulAut.conj_apply]
    have hp'cen : ∀ p ∈ T ⊓ K, p * p' = p' * p := by
      intro p hp
      have hpa : a * p * a⁻¹ ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom :=
        Subgroup.mem_map.2 ⟨p, hp, by simp [MulAut.conj_apply]⟩
      have h1 : r * (a * p * a⁻¹) = (a * p * a⁻¹) * r := hrc _ (hTS (A.Pa_le hpa))
      have h2 : u * (a * p * a⁻¹) = (a * p * a⁻¹) * u := A.comm u hu _ hpa
      rw [hruu] at h1
      have h3 : u' * (a * p * a⁻¹) = (a * p * a⁻¹) * u' := by
        have h4 : u * (u' * (a * p * a⁻¹)) = u * ((a * p * a⁻¹) * u') := by
          calc u * (u' * (a * p * a⁻¹)) = u * u' * (a * p * a⁻¹) := by group
            _ = (a * p * a⁻¹) * (u * u') := h1
            _ = ((a * p * a⁻¹) * u) * u' := by group
            _ = (u * (a * p * a⁻¹)) * u' := by rw [h2]
            _ = u * ((a * p * a⁻¹) * u') := by group
        exact mul_left_cancel h4
      rw [hu'eq] at h3
      have h5 : a * (p' * p) * a⁻¹ = a * (p * p') * a⁻¹ := by
        calc a * (p' * p) * a⁻¹ = a * p' * a⁻¹ * (a * p * a⁻¹) := by group
          _ = a * p * a⁻¹ * (a * p' * a⁻¹) := h3
          _ = a * (p * p') * a⁻¹ := by group
      have h6 : p' * p = p * p' := by
        have := congrArg (fun t => a⁻¹ * t * a) h5
        simpa [mul_assoc] using this
      exact h6.symm
    have hxz' : x * z = z * x := hxc z A.z_mem.1
    rcases hz'u u hu hucen with hu1 | huz <;> rcases hz'u p' hp' hp'cen with hp1 | hpz
    · left; rw [hruu, hu1, hu'eq, hp1]; group
    · exfalso
      have hrx : r = x := by rw [hruu, hu1, hu'eq, hpz, A.hxz, one_mul]
      apply hxz_ne
      rw [← A.hxa, ← hrx, hra]
    · exfalso
      have hrz : r = z := by rw [hruu, huz, hu'eq, hp1]; group
      apply hxz_ne
      rw [← A.hxz, ← hrz, hra]
    · right
      rw [hruu, huz, hu'eq, hpz, A.hxz, hxz']

theorem AlphaSetup.exists_conj_z_mul_eq_xz (A : AlphaSetup x K T a z psi) {s : G}
    (hsPa : s ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom) (hss : s * s = 1) (hs1 : s ≠ 1) :
    ∃ w : G, w * (z * s) * w⁻¹ = x * z := by
  obtain ⟨p₀, hp₀, hp₀s⟩ := Subgroup.mem_map.1 hsPa
  have hseq : s = a * p₀ * a⁻¹ := by rw [← hp₀s]; simp [MulAut.conj_apply]
  have hp₀p₀ : p₀ * p₀ = 1 := by
    have : a * (p₀ * p₀) * a⁻¹ = 1 := by
      calc a * (p₀ * p₀) * a⁻¹ = (a * p₀ * a⁻¹) * (a * p₀ * a⁻¹) := by group
        _ = 1 := by rw [← hseq, hss]
    calc p₀ * p₀ = a⁻¹ * (a * (p₀ * p₀) * a⁻¹) * a := by group
      _ = 1 := by rw [this]; group
  have hp₀1 : p₀ ≠ 1 := by
    intro h; apply hs1; rw [hseq, h]; group
  have hp₀C : p₀ ∈ centralizer ({x} : Set G) := A.T_le_C hp₀.1
  have hxC : x ∈ centralizer ({x} : Set G) := A.T_le_C A.x_mem_T
  have hzC : z ∈ centralizer ({x} : Set G) := A.T_le_C A.z_mem.1
  obtain ⟨i, hi⟩ := A.psi_P p₀ hp₀
  have hii : a7P i * a7P i = 1 := by
    rw [← hi, ← A.psiD.mul p₀ hp₀C p₀ hp₀C, hp₀p₀, A.psiD.one]
  have hi1 : a7P i ≠ 1 := by
    intro h
    have hodd := A.psiD.ker_odd p₀ hp₀.2 (hi.trans h)
    have h2 : orderOf p₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hp₀p₀) hp₀1
    rw [h2] at hodd
    exact absurd hodd (by decide)
  obtain ⟨g, hg, hgi⟩ := exists_even_conj_a7P_one i hii hi1
  have hxp : x * p₀ = p₀ * x := (mem_centralizer_singleton_iff.1 hp₀C).symm
  have hzp : z * p₀ = p₀ * z := A.z_central p₀ hp₀.1
  have hxz : x * z = z * x := (mem_centralizer_singleton_iff.1 hzC).symm
  have hff : (x * p₀) * (x * p₀) = 1 := by
    calc (x * p₀) * (x * p₀) = x * (p₀ * x) * p₀ := by group
      _ = x * (x * p₀) * p₀ := by rw [hxp]
      _ = (x * x) * (p₀ * p₀) := by group
      _ = 1 := by rw [A.x_sq, hp₀p₀, one_mul]
  have hmm : (z * p₀) * (z * p₀) = 1 := by
    calc (z * p₀) * (z * p₀) = z * (p₀ * z) * p₀ := by group
      _ = z * (z * p₀) * p₀ := by rw [hzp]
      _ = (z * z) * (p₀ * p₀) := by group
      _ = 1 := by rw [A.z_sq, hp₀p₀, one_mul]
  have hfm : (z * p₀) * (x * p₀) = (x * p₀) * (z * p₀) := by
    calc (z * p₀) * (x * p₀) = z * (p₀ * x) * p₀ := by group
      _ = z * (x * p₀) * p₀ := by rw [hxp]
      _ = (z * x) * p₀ * p₀ := by group
      _ = (x * z) * p₀ * p₀ := by rw [hxz]
      _ = x * (z * p₀) * p₀ := by group
      _ = x * (p₀ * z) * p₀ := by rw [hzp]
      _ = (x * p₀) * (z * p₀) := by group
  have hpsif : psi (x * p₀) = a7P i := by
    rw [A.psiD.mul x hxC p₀ hp₀C, A.psi_x, hi, one_mul]
  have hpsim : psi (z * p₀) = a7P 1 * a7P i := by
    rw [A.psiD.mul z hzC p₀ hp₀C, A.psi_z, hi]
  have hgc : g * psi (x * p₀) * g⁻¹ = psi (z * p₀) * psi (x * p₀) := by
    rw [hpsif, hpsim, hgi, mul_assoc, hii, mul_one]
  obtain ⟨h, hh⟩ := A.psiD.exists_conj_step ((centralizer ({x} : Set G)).mul_mem hxC hp₀C)
    (K.mul_mem A.z_mem.2 hp₀.2) hff hmm hfm hg hgc
  refine ⟨h * a⁻¹, ?_⟩
  have hae : a⁻¹ * (z * s) * a = x * p₀ := by
    have hx : x = a⁻¹ * z * a := by rw [← A.hxa]; group
    rw [hseq, hx]; group
  calc h * a⁻¹ * (z * s) * (h * a⁻¹)⁻¹ = h * (a⁻¹ * (z * s) * a) * h⁻¹ := by group
    _ = h * (x * p₀) * h⁻¹ := by rw [hae]
    _ = (z * p₀) * (x * p₀) := hh
    _ = (x * z) * (p₀ * p₀) := by
        calc (z * p₀) * (x * p₀) = z * (p₀ * x) * p₀ := by group
          _ = z * (x * p₀) * p₀ := by rw [hxp]
          _ = (z * x) * (p₀ * p₀) := by group
          _ = (x * z) * (p₀ * p₀) := by rw [hxz]
    _ = x * z := by rw [hp₀p₀, mul_one]

end BetaE

end CFSG.GH74.GLS.Th2.AlphaStep
