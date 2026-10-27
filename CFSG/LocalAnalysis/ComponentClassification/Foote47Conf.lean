module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P2
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Transport

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_inf_coreActionKernel {X : Subgroup G} {t g : G}
    (hgX : g ∈ normalizer (X : Set G)) (hgt : g ∈ centralizer ({t} : Set G)) :
    g ∈ normalizer ((centralizer ({t} : Set G) ⊓ coreActionKernel X : Subgroup G) : Set G) :=
  mem_normalizer_inf' (le_normalizer hgt) (mem_normalizer_coreActionKernel hgX)

omit [Finite G] in
theorem isSylowOf_conjugate [Finite G] {T Y : Subgroup G} (hT : IsSylowOf 2 T Y) (g : G) :
    IsSylowOf 2 (conjugate T g) (conjugate Y g) := by
  have h1 := isSylowOf_map_conj hT g⁻¹
  unfold CFSG.conjugate
  exact h1

theorem inf_centralizer_facts (h : FooteSec4 G L) {M T Q₀ : Subgroup G} {t z : G}
    (hv : Viol L M t) (hT : IsSylowOf 2 T (coreActionKernel M)) (htT : t ∈ T)
    (hd : TwoData T t z Q₀)
    (hQX : IsSylowOf 2 (T ⊓ centralizer ({t} : Set G))
      (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L z))) :
    T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel (footeF L t) ∧
      (∀ d ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
        d ∈ coreActionKernel (footeF L t) → d ∈ coreActionKernel (footeF L z)) ∧
      IsSylowOf 2 (T ⊓ centralizer ({t} : Set G))
        (centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have dz := zData_of h hv.hM hT hd.hz hd.hzT hd.hzc
  have htK : t ∈ coreActionKernel (footeF L z) := dz.hTKle htT
  obtain ⟨hB, -, -, -, hfix⟩ := footeF_spec h dz.hKmax dz.hKF hv.ht htK
  have hKb : IsTwoComponentAt t (footeFixed (footeF L z) t) := hfix ▸ hB
  have h1 : T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel (footeF L t) := fun x hx =>
    FooteLit.mem_coreActionKernel_footeF h dz.hKmax dz.hKF hv.ht htK
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2).symm (dz.hTKle (mem_inf.mp hx).1)
  have h2 : ∀ d ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
      d ∈ coreActionKernel (footeF L t) → d ∈ coreActionKernel (footeF L z) := by
    intro d hd hdC
    rw [← hfix] at hdC
    exact (mem_coreActionKernel_iff_of_footeFixed dz.hKmax.1 hv.ht htK hKb
      (dz.centralizer_le_normalizer h (mem_inf.mp hd).1) hdC.1 (mem_inf.mp hd).2).mpr hdC
  refine ⟨h1, h2, ?_⟩
  set Q := T ⊓ centralizer ({t} : Set G) with hQ
  have hQp : IsPGroup 2 Q := hT.isPGroup.to_le inf_le_left
  obtain ⟨Q₁, hQ₁, hQQ₁⟩ := exists_isSylowOf_ge_of_le (le_inf inf_le_right h1) hQp
  suffices hQ₁eq : Q₁ = Q by rw [← hQ₁eq]; exact hQ₁
  by_contra hne
  have hlt : Q < Q₁ := lt_of_le_of_ne hQQ₁ (Ne.symm hne)
  obtain ⟨x, hxQ₁, hxQ, hxN⟩ := exists_mem_normalizer_of_lt hQ₁.isPGroup hlt
  have hNz := hd.normalizer_le_centralizer (by rw [← sq, ← hv.ht]; exact pow_orderOf_eq_one t)
  have hY : Q₁ ⊓ normalizer ((Q : Subgroup G) : Set G) = Q := by
    refine hQX.eq_of_le (le_inf hQQ₁ le_normalizer) (fun y hy => ?_)
      (hQ₁.isPGroup.to_le inf_le_left)
    have hyz := hNz (mem_inf.mp hy).2
    have hyC := hQ₁.le (mem_inf.mp hy).1
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hyz, (mem_inf.mp hyC).1⟩,
      h2 y (mem_inf.mpr ⟨hyz, (mem_inf.mp hyC).1⟩) (mem_inf.mp hyC).2⟩
  exact hxQ (hY ▸ mem_inf.mpr ⟨hxQ₁, hxN⟩)

structure Conf (L M T S P : Subgroup G) (t z : G) : Prop where
  hv : Viol L M t
  hSN : IsSylowOf 2 S (normalizer (M : Set G))
  hSz : IsSylowOf 2 S (centralizer ({z} : Set G))
  hT : T = S ⊓ coreActionKernel M
  hTsyl : IsSylowOf 2 T (coreActionKernel M)
  htT : t ∈ T
  hd : ∃ Q₀ : Subgroup G, TwoData T t z Q₀
  hP : P = S ⊓ centralizer ({t} : Set G)
  hPsyl : IsSylowOf 2 P (centralizer ({t} : Set G))
  hQX : IsSylowOf 2 (T ⊓ centralizer ({t} : Set G))
    (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L z))
  hQF : T ⊓ centralizer ({t} : Set G) ≤ coreActionKernel (footeF L t)
  hFK : ∀ d ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
    d ∈ coreActionKernel (footeF L t) → d ∈ coreActionKernel (footeF L z)
  hQP : P ⊓ coreActionKernel (footeF L t) = T ⊓ centralizer ({t} : Set G)

theorem exists_conf (h : FooteSec4 G L) {M T Q₀ : Subgroup G} {t z : G} (hv : Viol L M t)
    (hT : IsSylowOf 2 T (coreActionKernel M)) (htT : t ∈ T) (hd : TwoData T t z Q₀)
    (hQX : IsSylowOf 2 (T ⊓ centralizer ({t} : Set G))
      (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L z))) :
    ∃ M₁ T₁ S P : Subgroup G, Conf L M₁ T₁ S P t z ∧
      T₁ ⊓ centralizer ({t} : Set G) = T ⊓ centralizer ({t} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQF, hFK, hQsylF⟩ := inf_centralizer_facts h hv hT htT hd hQX
  have dz := zData_of h hv.hM hT hd.hz hd.hzT hd.hzc
  set K := footeF L z with hK
  set Q := T ⊓ centralizer ({t} : Set G) with hQ
  set X := centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ⊓ coreActionKernel K with hX
  have htt : t * t = 1 := by rw [← sq, ← hv.ht]; exact pow_orderOf_eq_one t
  have hQp : IsPGroup 2 Q := hT.isPGroup.to_le inf_le_left
  have hNz : normalizer ((Q : Subgroup G) : Set G) ≤ centralizer ({z} : Set G) :=
    hd.normalizer_le_centralizer htt
  have hTz : T ≤ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hd.hzc x hx)
  have hCtF : centralizer ({t} : Set G) ≤ normalizer (footeF L t : Set G) := by
    obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hv.hM hv.ht hv.htC
    exact le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge_of_le (inf_le_right : Q ≤ centralizer ({t} : Set G))
    hQp
  have hPF : P ⊓ coreActionKernel (footeF L t) = Q := by
    have h1 := hP.inf_of_le_normalizer (inf_le_left : centralizer ({t} : Set G) ⊓
      coreActionKernel (footeF L t) ≤ _) fun g hg =>
        mem_normalizer_inf_coreActionKernel (hCtF hg) hg
    have h2 : P ⊓ (centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L t)) =
        P ⊓ coreActionKernel (footeF L t) := by
      rw [← inf_assoc, inf_eq_left.mpr hP.le]
    rw [h2] at h1
    exact hQsylF.eq_of_le (le_inf hQP hQF) h1.le h1.isPGroup
  have hPz : P ≤ centralizer ({z} : Set G) := fun g hg => hNz (by
    rw [← hPF]
    exact mem_normalizer_inf' (le_normalizer hg)
      (mem_normalizer_coreActionKernel (hCtF (hP.le hg))))
  obtain ⟨E, hET, hE2, hE8⟩ := exists_card_eight_le_of_isSylowOf h hv.hM hT
  have hEC : E ≤ coreActionKernel M ⊓ centralizer ({z} : Set G) :=
    le_inf (hET.trans hT.le) (hET.trans hTz)
  obtain ⟨-, -, -, P₀, hP₀, hP₀N⟩ := foote_lemma_4_5_iv h hv.hM hd.hz dz.hzC hE2 hE8 hEC
  set Y := normalizer (M : Set G) ⊓ centralizer ({z} : Set G) with hY
  have hP₀Y : IsSylowOf 2 P₀ Y := hP₀.of_le (le_inf hP₀N hP₀.le) inf_le_right
  have hTY : T ≤ Y := le_inf (fun x hx => (hT.le hx).1) hTz
  obtain ⟨S₀, hS₀Y, hTS₀⟩ := exists_isSylowOf_ge_of_le hTY hT.isPGroup
  have hS₀z : IsSylowOf 2 S₀ (centralizer ({z} : Set G)) := by
    refine isSylowOf_of_card (hS₀Y.le.trans inf_le_right) ?_
    rw [hS₀Y.card_eq, ← hP₀Y.card_eq, hP₀.card_eq]
  have hCMN : coreActionKernel M ≤ normalizer (M : Set G) := fun x hx => hx.1
  obtain ⟨S₂, hS₂, hS₀S₂⟩ := exists_isSylowOf_ge_of_le (hS₀Y.le.trans inf_le_left)
    hS₀Y.isPGroup
  have hT₂ := hS₂.inf_of_le_normalizer hCMN fun g hg => mem_normalizer_coreActionKernel hg
  have hT₂eq : S₂ ⊓ coreActionKernel M = T :=
    hT.eq_of_le (le_inf (hTS₀.trans hS₀S₂) hT.le) hT₂.le hT₂.isPGroup
  have hS₂z : S₂ ≤ centralizer ({z} : Set G) := by
    intro s hs
    have hsT : ∀ x ∈ T, s * x * s⁻¹ ∈ T := fun x hx => by
      rw [← hT₂eq] at hx ⊢
      exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hx).1) (inv_mem hs),
        (mem_normalizer_iff.mp (mem_normalizer_coreActionKernel (hS₂.le hs)) x).mp
          (mem_inf.mp hx).2⟩
    have hsz : s * z * s⁻¹ = z := by
      refine hd.hzZ _ (hsT z hd.hzT) ?_ fun y hy => ?_
      · rw [show s * z * s⁻¹ = MulAut.conj s z from rfl, MulEquiv.orderOf_eq, hd.hz]
      · have hy' : s⁻¹ * y * s ∈ T := by
          have := hsT _ (show s⁻¹ * y * s⁻¹⁻¹ ∈ T from by
            rw [← hT₂eq] at hy ⊢
            exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) (mem_inf.mp hy).1)
              (inv_mem (inv_mem hs)), (mem_normalizer_iff.mp (inv_mem
                (mem_normalizer_coreActionKernel (hS₂.le hs))) y).mp (mem_inf.mp hy).2⟩)
          rw [show s * (s⁻¹ * y * s⁻¹⁻¹) * s⁻¹ = y by group] at this
          rw [show s⁻¹ * y * s = s⁻¹ * y * s⁻¹⁻¹ by group]
          rw [← hT₂eq] at hy ⊢
          exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) (mem_inf.mp hy).1)
            (inv_mem (inv_mem hs)), (mem_normalizer_iff.mp (inv_mem
              (mem_normalizer_coreActionKernel (hS₂.le hs))) y).mp (mem_inf.mp hy).2⟩
        have h1 := hd.hzc _ hy'
        calc s * z * s⁻¹ * y = s * (z * (s⁻¹ * y * s)) * s⁻¹ := by group
          _ = s * ((s⁻¹ * y * s) * z) * s⁻¹ := by rw [h1]
          _ = y * (s * z * s⁻¹) := by group
    rw [mem_centralizer_singleton_iff]
    calc s * z = s * z * s⁻¹ * s := by group
      _ = z * s := by rw [hsz]
  have hS₂eq : S₂ = S₀ := hS₀z.eq_of_le hS₀S₂ hS₂z hS₂.isPGroup
  rw [hS₂eq] at hS₂ hT₂eq
  obtain ⟨k, hkz, hk⟩ := exists_conj_le_of_isSylowOf hS₀z hPz hP.isPGroup
  set c := k⁻¹ with hc
  set M₁ := conjugate M c with hM₁
  set S₁ := conjugate S₀ c with hS₁
  set T₁ := conjugate T c with hT₁
  have hmemS₁ : ∀ x, x ∈ S₁ ↔ k⁻¹ * x * k ∈ S₀ := fun x => by
    rw [hS₁, mem_conjugate_iff, hc, inv_inv]
  have hPS₁ : P ≤ S₁ := fun x hx => (hmemS₁ x).mpr (hk x hx)
  have hcz : c ∈ centralizer ({z} : Set G) := inv_mem hkz
  have hCz : conjugate (centralizer ({z} : Set G)) c = centralizer ({z} : Set G) :=
    conjugate_eq_of_mem_normalizer (le_normalizer hcz)
  have hM₁F : IsFooteM L M₁ := isFooteM_conjugate h hv.hM c
  have hS₁N : IsSylowOf 2 S₁ (normalizer (M₁ : Set G)) := by
    rw [hM₁, ← GSThmB.conjugate_normalizer]
    exact isSylowOf_conjugate hS₂ c
  have hS₁z : IsSylowOf 2 S₁ (centralizer ({z} : Set G)) := by
    rw [← hCz]
    exact isSylowOf_conjugate hS₀z c
  have hT₁eq : T₁ = S₁ ⊓ coreActionKernel M₁ := by
    rw [hT₁, hS₁, hM₁, coreActionKernel_conjugate, ← GSThmB.conjugate_inf, hT₂eq]
  have hT₁C : IsSylowOf 2 T₁ (coreActionKernel M₁) := by
    rw [hT₁, hM₁, coreActionKernel_conjugate]
    exact isSylowOf_conjugate hT c
  have hT₁z : T₁ ≤ centralizer ({z} : Set G) := hT₁eq ▸ inf_le_left.trans hS₁z.le
  have hzT₁ : z ∈ T₁ := by
    rw [hT₁, mem_conjugate_iff, hc, inv_inv,
      show k⁻¹ * z * k = z by rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hkz,
        inv_mul_cancel_left]]
    exact hd.hzT
  have dz₁ := zData_of h hM₁F hT₁C hd.hz hzT₁ fun x hx =>
    mem_centralizer_singleton_iff.mp (hT₁z hx)
  have hQT₁ : Q ≤ T₁ := by
    intro x hx
    rw [hT₁eq]
    refine mem_inf.mpr ⟨hPS₁ (hQP hx), ?_⟩
    exact dz₁.mem_coreActionKernel (dz.hTKle (mem_inf.mp hx).1) (hS₁N.le (hPS₁ (hQP hx)))
  have hT₁Q : T₁ ⊓ centralizer ({t} : Set G) = Q :=
    hQX.eq_of_le (le_inf hQT₁ inf_le_right)
      (fun x hx => mem_inf.mpr ⟨mem_inf.mpr ⟨hT₁z (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩,
        dz₁.hTKle (mem_inf.mp hx).1⟩) (hT₁C.isPGroup.to_le inf_le_left)
  have htT₁ : t ∈ T₁ := hQT₁ (mem_inf.mpr ⟨htT, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hQM₁ : Q ≤ coreActionKernel M₁ ⊓ centralizer ({t} : Set G) := fun x hx =>
    mem_inf.mpr ⟨hT₁C.le (hQT₁ hx), (mem_inf.mp hx).2⟩
  obtain ⟨Q'', hQ'', hQQ''⟩ := exists_isSylowOf_ge_of_le hQM₁ hQp
  have hQ''eq : Q'' = Q := by
    by_contra hne
    have hlt : Q < Q'' := lt_of_le_of_ne hQQ'' (Ne.symm hne)
    obtain ⟨x, hxQ'', hxQ, hxN⟩ := exists_mem_normalizer_of_lt hQ''.isPGroup hlt
    have hY' : Q'' ⊓ normalizer ((Q : Subgroup G) : Set G) = Q := by
      refine hQX.eq_of_le (le_inf hQQ'' le_normalizer) (fun y hy => ?_)
        (hQ''.isPGroup.to_le inf_le_left)
      have hyz := hNz (mem_inf.mp hy).2
      have hyC := hQ''.le (mem_inf.mp hy).1
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hyz, (mem_inf.mp hyC).2⟩,
        dz₁.mem_coreActionKernel_footeF h (mem_inf.mp hyC).1 hyz⟩
    exact hxQ (hY' ▸ mem_inf.mpr ⟨hxQ'', hxN⟩)
  have hnoQ : NoEight Q := fun F hFQ hF2 hF8 =>
    hv.hno F (hFQ.trans (le_inf (inf_le_left.trans hT.le) inf_le_right)) hF2 hF8
  have hv₁ : Viol L M₁ t :=
    ⟨hM₁F, hv.ht, hT₁C.le htT₁, NoEight.of_isSylowOf (hQ''eq ▸ hQ'') hnoQ⟩
  obtain ⟨E₁, hE₁T, hE₁2, hE₁8⟩ := exists_card_eight_le_of_isSylowOf h hM₁F hT₁C
  obtain ⟨z', Q₀', hd'⟩ := exists_twoData hT₁C.isPGroup hE₁T hE₁2 hE₁8 htT₁ hv.ht
    (by rw [hT₁Q]; exact hnoQ)
  have hzz' : z = z' := hd'.hzZ z hzT₁ hd.hz fun y hy =>
    (mem_centralizer_singleton_iff.mp (hT₁z hy)).symm
  rw [← hzz'] at hd'
  have hPeq : P = S₁ ⊓ centralizer ({t} : Set G) :=
    (hP.eq_of_le (le_inf hPS₁ hP.le) inf_le_right (hS₁z.isPGroup.to_le inf_le_left)).symm
  refine ⟨M₁, T₁, S₁, P, ⟨hv₁, hS₁N, hS₁z, hT₁eq, hT₁C, htT₁, ⟨Q₀', hd'⟩, hPeq, hP,
    hT₁Q ▸ hQX, hT₁Q ▸ hQF, hFK, hT₁Q ▸ hPF⟩, hT₁Q⟩

end CFSG.ComponentClassification.Foote47
