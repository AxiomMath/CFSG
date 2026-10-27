module

public import CFSG.FeitThompson.Local.PrimeFixedSectionExtension
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.FixedFreeComplementsInvariantSections
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

variable {X : Type*} [Group X]

theorem IsElementaryAbelian.map {p : ℕ} {G H : Type*} [Group G] [Group H] {A : Subgroup G}
    (hA : IsElementaryAbelian p A) (f : G →* H) : IsElementaryAbelian p (A.map f) := by
  rw [isElementaryAbelian_iff]
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul, hA.mul_comm ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.pow_eq_one ha, map_one]

theorem centralizer_coe_zpowers {G : Type*} [Group G] (x : G) :
    centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem mem_inf_centralizer_map_mk'_iff {N A : Subgroup X} [N.Normal] {V : Subgroup (X ⧸ N)}
    {v : X ⧸ N} : v ∈ V ⊓ centralizer ((A.map (mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) ↔
      v ∈ V ∧ ∀ a ∈ A, (mk a : X ⧸ N) * v * (mk a : X ⧸ N)⁻¹ = v := by
  rw [Subgroup.mem_inf, mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun hc a ha => ?_, fun hc w hw => ?_⟩
  · rw [hc (mk a) ⟨a, ha, rfl⟩]; group
  · obtain ⟨a, ha, rfl⟩ := hw
    rw [mk'_apply]
    calc (mk a : X ⧸ N) * v = (mk a : X ⧸ N) * v * (mk a : X ⧸ N)⁻¹ * (mk a : X ⧸ N) := by group
      _ = v * mk a := by rw [hc a ha]

theorem exists_mem_inf_centralizer_mul_eq [Finite X] {T I R : Subgroup X}
    [Group.IsSolvable ↥T] [Group.IsSolvable ↥R] (hcop : (Nat.card ↥R).Coprime (Nat.card ↥T))
    (hTI : T ≤ normalizer (I : Set X)) (hRT : R ≤ normalizer (T : Set X))
    (hRI : R ≤ normalizer (I : Set X)) {x : X} (hx : x ∈ T)
    (hfix : ∀ r ∈ R, x⁻¹ * (r * x * r⁻¹) ∈ I) :
    ∃ z ∈ T ⊓ centralizer (R : Set X), ∃ n ∈ I ⊓ T, x = z * n := by
  have hIn : (I.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTI
  have hinv : IsInvariantSubgroup (conjOnNormalized T hRT) (I.subgroupOf T) :=
    isInvariantSubgroup_subgroupOf hRT hRI
  have hv : ∀ b : ↥R, (⟨x, hx⟩ : ↥T)⁻¹ * conjOnNormalized T hRT b ⟨x, hx⟩ ∈ I.subgroupOf T := by
    intro b
    rw [mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, conjOnNormalized_apply_coe]
    exact hfix b b.2
  obtain ⟨n, hnI, hnfix⟩ := exists_mem_forall_apply_mul_eq hinv hcop hv
  have hcent : x * (n : X) ∈ centralizer (R : Set X) := by
    rw [mem_centralizer_iff]
    intro g hg
    have hh := congrArg (Subtype.val (p := fun z : X => z ∈ T)) (hnfix ⟨g, hg⟩)
    rw [conjOnNormalized_apply_coe, Subgroup.coe_mul] at hh
    calc g * (x * (n : X)) = g * (x * (n : X)) * g⁻¹ * g := by group
      _ = x * (n : X) * g := by rw [hh]
  exact ⟨x * (n : X), ⟨T.mul_mem hx n.2, hcent⟩, (n : X)⁻¹,
    ⟨I.inv_mem (mem_subgroupOf.1 hnI), T.inv_mem n.2⟩, by group⟩

theorem inf_centralizer_map_mk'_eq_map [Finite X] {N Q A : Subgroup X} [N.Normal]
    [Group.IsSolvable ↥Q] [Group.IsSolvable ↥A] (hcop : (Nat.card ↥A).Coprime (Nat.card ↥Q))
    (hAQ : A ≤ normalizer (Q : Set X)) :
    Q.map (mk' N) ⊓ centralizer ((A.map (mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N))
      = (Q ⊓ centralizer (A : Set X)).map (mk' N) := by
  refine le_antisymm (fun v hv => ?_) ?_
  · obtain ⟨⟨x, hxQ, hxv⟩, hvc⟩ := hv
    have hfix : ∀ r ∈ A, x⁻¹ * (r * x * r⁻¹) ∈ N := by
      intro r hr
      have hcomm := mem_centralizer_iff.1 hvc (mk r) ⟨r, hr, rfl⟩
      rw [← hxv] at hcomm
      simp only [mk'_apply] at hcomm
      rw [← QuotientGroup.eq]
      calc (mk x : X ⧸ N) = mk r * mk x * (mk r)⁻¹ := by rw [hcomm]; group
        _ = mk (r * x * r⁻¹) := by
            simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    obtain ⟨z, hz, n, hn, hxzn⟩ :=
      exists_mem_inf_centralizer_mul_eq hcop le_normalizer_of_normal hAQ
        le_normalizer_of_normal hxQ hfix
    refine ⟨z, hz, ?_⟩
    rw [mk'_apply, ← hxv, mk'_apply, QuotientGroup.eq, hxzn]
    simpa using N.inv_mem hn.1
  · rintro _ ⟨x, ⟨hxQ, hxc⟩, rfl⟩
    refine ⟨⟨x, hxQ, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    simp only [mk'_apply, ← QuotientGroup.mk_mul]
    rw [mem_centralizer_iff.1 hxc r hr]

noncomputable def normalizerQuotientEquiv (I : Subgroup X) [I.Normal] :
    normalizerQuotient I ≃* X ⧸ I :=
  (QuotientGroup.quotientMulEquivOfEq (M := I.subgroupOf (normalizer (I : Set X)))
      (by rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((mk' I).comp (normalizer (I : Set X)).subtype)
      (by
        intro z
        induction z using QuotientGroup.induction_on with
        | _ x => exact ⟨⟨x, by rw [Subgroup.normalizer_eq_top]; exact mem_top x⟩, rfl⟩))

theorem surjective_normalizerQuotientEquiv (I : Subgroup X) [I.Normal] :
    Function.Surjective (normalizerQuotientEquiv I).toMonoidHom :=
  (normalizerQuotientEquiv I).surjective

theorem normalizerQuotientEquiv_mk (I : Subgroup X) [I.Normal] (x : ↥(normalizer (I : Set X))) :
    normalizerQuotientEquiv I (QuotientGroup.mk x) = QuotientGroup.mk (x : X) := (rfl)

theorem mk_mem_map_mk'_iff (I S : Subgroup X) [I.Normal] (y : ↥(normalizer (I : Set X))) :
    (QuotientGroup.mk (y : X) : X ⧸ I) ∈ S.map (mk' I) ↔
      (QuotientGroup.mk y : normalizerQuotient I) ∈ normalizerQuotientMap I S := by
  rw [show (QuotientGroup.mk y : normalizerQuotient I) = QuotientGroup.mk ⟨(y : X), y.2⟩ from rfl,
    mk_mem_normalizerQuotientMap_iff y.2]
  constructor
  · rintro ⟨s, hs, hsy⟩
    refine ⟨s, hs, by rw [Subgroup.normalizer_eq_top]; exact mem_top s, ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    rw [mk'_apply, QuotientGroup.eq] at hsy
    exact hsy
  · rintro ⟨u, hu, _, huy⟩
    rw [QuotientGroup.eq, mem_subgroupOf] at huy
    exact ⟨u, hu, by rw [mk'_apply, QuotientGroup.eq]; exact huy⟩

theorem comap_normalizerQuotientEquiv (I S : Subgroup X) [I.Normal] :
    (S.map (mk' I)).comap (normalizerQuotientEquiv I).toMonoidHom = normalizerQuotientMap I S := by
  ext z
  induction z using QuotientGroup.induction_on with
  | _ y =>
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, normalizerQuotientEquiv_mk,
      mk_mem_map_mk'_iff]

theorem map_normalizerQuotientEquiv (I S : Subgroup X) [I.Normal] :
    (normalizerQuotientMap I S).map (normalizerQuotientEquiv I).toMonoidHom = S.map (mk' I) := by
  rw [← comap_normalizerQuotientEquiv I S,
    Subgroup.map_comap_eq_self_of_surjective (surjective_normalizerQuotientEquiv I)]

theorem forall_normal_lt_map_mk'_eq_bot_of_forall (I S : Subgroup X) [I.Normal]
    (hmin : ∀ M : Subgroup (normalizerQuotient I), M.Normal → M < normalizerQuotientMap I S →
      M = ⊥) {M : Subgroup (X ⧸ I)} (hM : M.Normal) (hlt : M < S.map (mk' I)) : M = ⊥ := by
  have hcomap : M.comap (normalizerQuotientEquiv I).toMonoidHom = ⊥ := by
    refine hmin _ (hM.comap _) ?_
    rw [← comap_normalizerQuotientEquiv I S]
    exact lt_of_le_of_ne (Subgroup.comap_mono hlt.le) fun heq =>
      hlt.ne (Subgroup.comap_injective (surjective_normalizerQuotientEquiv I) heq)
  rw [← Subgroup.map_comap_eq_self_of_surjective (surjective_normalizerQuotientEquiv I) M, hcomap,
    Subgroup.map_bot]

variable {q : ℕ} {Q D K Z : Subgroup X}

namespace IsPrimeFixedSectionSetup

theorem sup_eq_top (h : IsPrimeFixedSectionSetup X q Q D K Z) : Q ⊔ (D ⊔ K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x ∈ (Q : Set X) * ((D ⊔ K : Subgroup X) : Set X) := by rw [h.coe_mul_coe]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem D_le_normalizer_inf_centralizer (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    D ≤ normalizer ((Q ⊓ centralizer (D : Set X) : Subgroup X) : Set X) := by
  have := h.normal_Q
  exact le_trans (le_inf le_normalizer_of_normal
      (le_trans le_normalizer (normalizer_le_normalizer_centralizer D)))
    Subgroup.inf_normalizer_le_normalizer_inf

theorem K_le_normalizer_inf_centralizer (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    K ≤ normalizer ((Q ⊓ centralizer (D : Set X) : Subgroup X) : Set X) := by
  have := h.normal_Q
  have := h.normal_D
  refine le_trans (le_inf le_normalizer_of_normal
      (le_trans ?_ (normalizer_le_normalizer_centralizer D)))
    Subgroup.inf_normalizer_le_normalizer_inf
  exact le_trans le_sup_right (Subgroup.le_normalizer_of_normal_subgroupOf
    (H := D) (K := D ⊔ K) le_sup_left)

theorem sup_le_normalizer_inf_centralizer (h : IsPrimeFixedSectionSetup X q Q D K Z) :
    (D ⊔ K : Subgroup X) ≤ normalizer ((Q ⊓ centralizer (D : Set X) : Subgroup X) : Set X) :=
  sup_le h.D_le_normalizer_inf_centralizer h.K_le_normalizer_inf_centralizer

theorem coprime_natCard_Q_of_le_sup (h : IsPrimeFixedSectionSetup X q Q D K Z) {A : Subgroup X}
    (hA : A ≤ D ⊔ K) : (Nat.card ↥A).Coprime (Nat.card ↥Q) :=
  (h.coprime_Q.coprime_dvd_right (card_dvd_of_le hA)).symm

end IsPrimeFixedSectionSetup

namespace IsPrimeFixedSectionSetup

variable (h : IsPrimeFixedSectionSetup X q Q D K Z)
  (hQ0 : Q ⊓ centralizer (D : Set X) < Q)

include h hQ0

theorem le_normalizer_and_minimal :
    Q ≤ normalizer ((Q ⊓ centralizer (D : Set X) : Subgroup X) : Set X) ∧
      Z ⊓ (Q ⊓ centralizer (D : Set X)) = ⊥ ∧
      IsElementaryAbelian q (normalizerQuotientMap (Q ⊓ centralizer (D : Set X)) Q) ∧
      (∀ M : Subgroup (normalizerQuotient (Q ⊓ centralizer (D : Set X))), M.Normal →
        M < normalizerQuotientMap (Q ⊓ centralizer (D : Set X)) Q → M = ⊥) := by
  obtain ⟨T, hTQ, hDKT, hIT, -, -, -, hTe, hTm, hZT, hZI⟩ :=
    exists_le_inf_normalizer_isElementaryAbelian_minimal_normal h hQ0 hQ0 le_rfl
      h.sup_le_normalizer_inf_centralizer
  have hTeq : T = Q := by
    by_contra hne
    have hTlt : T < Q := lt_of_le_of_ne (le_trans hTQ inf_le_left) hne
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hZT'⟩ :=
      exists_le_inf_normalizer_isElementaryAbelian_minimal_normal h hQ0 hTlt hIT.le hDKT
    exact h.Z_ne_bot (by rw [← inf_eq_left.2 hZT, hZT'])
  subst hTeq
  exact ⟨le_trans hTQ inf_le_right, hZI, hTe, hTm⟩

theorem normal_inf_centralizer : (Q ⊓ centralizer (D : Set X) : Subgroup X).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h.sup_eq_top]
  exact sup_le (le_normalizer_and_minimal h hQ0).1 h.sup_le_normalizer_inf_centralizer

theorem inf_centralizer_inf_Z_eq_bot : (Q ⊓ centralizer (D : Set X)) ⊓ Z = ⊥ := by
  rw [inf_comm]
  exact (le_normalizer_and_minimal h hQ0).2.1

theorem disjoint_inf_centralizer_Z : Disjoint (Q ⊓ centralizer (D : Set X)) Z :=
  disjoint_iff.2 (inf_centralizer_inf_Z_eq_bot h hQ0)

theorem map_mk'_ne_bot :
    haveI := normal_inf_centralizer h hQ0
    Q.map (mk' (Q ⊓ centralizer (D : Set X))) ≠ ⊥ := by
  have := normal_inf_centralizer h hQ0
  rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact fun hle => hQ0.ne (le_antisymm hQ0.le hle)

theorem normal_map_mk' :
    haveI := normal_inf_centralizer h hQ0
    (Q.map (mk' (Q ⊓ centralizer (D : Set X)))).Normal := by
  have := normal_inf_centralizer h hQ0
  exact h.normal_Q.map _ (mk'_surjective _)

theorem isElementaryAbelian_map_mk' :
    haveI := normal_inf_centralizer h hQ0
    IsElementaryAbelian q (Q.map (mk' (Q ⊓ centralizer (D : Set X)))) := by
  have := normal_inf_centralizer h hQ0
  rw [← map_normalizerQuotientEquiv]
  exact ((le_normalizer_and_minimal h hQ0).2.2.1).map _

theorem forall_normal_lt_map_mk'_eq_bot :
    haveI := normal_inf_centralizer h hQ0
    ∀ M : Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X))), M.Normal →
      M < Q.map (mk' (Q ⊓ centralizer (D : Set X))) → M = ⊥ := by
  have := normal_inf_centralizer h hQ0
  exact fun M hM hlt =>
    forall_normal_lt_map_mk'_eq_bot_of_forall _ _ (le_normalizer_and_minimal h hQ0).2.2.2 hM hlt

theorem inf_centralizer_map_mk'_D_eq_bot :
    haveI := normal_inf_centralizer h hQ0
    Q.map (mk' (Q ⊓ centralizer (D : Set X))) ⊓
        centralizer ((D.map (mk' (Q ⊓ centralizer (D : Set X))) :
          Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
            Set (X ⧸ (Q ⊓ centralizer (D : Set X)))) = ⊥ := by
  have := normal_inf_centralizer h hQ0
  have : Finite X := h.finite
  have : Group.IsSolvable X := h.isSolvable
  have := h.normal_Q
  rw [inf_centralizer_map_mk'_eq_map (h.coprime_natCard_Q_of_le_sup le_sup_left)
    le_normalizer_of_normal, QuotientGroup.map_mk'_self]

theorem inf_centralizer_map_mk'_K_eq :
    haveI := normal_inf_centralizer h hQ0
    Q.map (mk' (Q ⊓ centralizer (D : Set X))) ⊓
        centralizer ((K.map (mk' (Q ⊓ centralizer (D : Set X))) :
          Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
            Set (X ⧸ (Q ⊓ centralizer (D : Set X))))
      = Z.map (mk' (Q ⊓ centralizer (D : Set X))) := by
  have := normal_inf_centralizer h hQ0
  have : Finite X := h.finite
  have : Group.IsSolvable X := h.isSolvable
  have := h.normal_Q
  rw [inf_centralizer_map_mk'_eq_map (h.coprime_natCard_Q_of_le_sup le_sup_right)
    le_normalizer_of_normal, ← h.Z_eq]

theorem natCard_map_mk'_Z :
    haveI := normal_inf_centralizer h hQ0
    Nat.card ↥(Z.map (mk' (Q ⊓ centralizer (D : Set X)))) = q := by
  have := normal_inf_centralizer h hQ0
  rw [← Subgroup.relIndex_ker Z (mk' _), QuotientGroup.ker_mk', Subgroup.relIndex,
    Subgroup.subgroupOf_eq_bot.2 (disjoint_inf_centralizer_Z h hQ0), Subgroup.index_bot,
    h.natCard_Z]

theorem inf_centralizer_map_mk'_singleton_eq {k : X} (hk : k ∈ K) (hk1 : k ≠ 1) :
    haveI := normal_inf_centralizer h hQ0
    Q.map (mk' (Q ⊓ centralizer (D : Set X))) ⊓
        centralizer (((zpowers k).map (mk' (Q ⊓ centralizer (D : Set X))) :
          Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
            Set (X ⧸ (Q ⊓ centralizer (D : Set X))))
      = Q.map (mk' (Q ⊓ centralizer (D : Set X))) ⊓
        centralizer ((K.map (mk' (Q ⊓ centralizer (D : Set X))) :
          Subgroup (X ⧸ (Q ⊓ centralizer (D : Set X)))) :
            Set (X ⧸ (Q ⊓ centralizer (D : Set X)))) := by
  have := normal_inf_centralizer h hQ0
  have : Finite X := h.finite
  have : Group.IsSolvable X := h.isSolvable
  have := h.normal_Q
  rw [inf_centralizer_map_mk'_eq_map
      (h.coprime_natCard_Q_of_le_sup (le_trans (zpowers_le_of_mem hk) le_sup_right))
      le_normalizer_of_normal,
    centralizer_coe_zpowers, h.inf_centralizer_Q k hk hk1,
    inf_centralizer_map_mk'_eq_map (h.coprime_natCard_Q_of_le_sup le_sup_right)
      le_normalizer_of_normal, ← h.Z_eq]

end IsPrimeFixedSectionSetup

end CFSG.FeitThompson
