module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerMinimal
import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedCentral
import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.GroupTheory.SteinbergBM
  CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem le_normalizer_of_conj_mem {A U : Subgroup G}
    (h : ∀ a ∈ A, ∀ x ∈ U, a * x * a⁻¹ ∈ U) : A ≤ normalizer (U : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h a ha x, fun hx => ?_⟩
  have h2 := h a⁻¹ (A.inv_mem ha) _ hx
  have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem frattini_irreducibility_of_minimal {q : ℕ} (hq : q.Prime) {A K M : Subgroup G}
    (hqA : ¬ q ∣ Nat.card A) (hqK : IsPGroup q K) (hAK : A ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M) (hnc : ¬ K ≤ centralizer (A : Set G))
    (hproper : ∀ U : Subgroup G, U < K → A ≤ normalizer (U : Set G) → U ≤ M) :
    ⁅K, A⁆ = K ∧ (frattini K).map K.subtype < K ∧ ∀ U : Subgroup G, U < K →
      A ≤ normalizer (U : Set G) → U ≤ (frattini K).map K.subtype := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  let _ : MulDistribMulAction A K := MulDistribMulAction.compHom K (Subgroup.inclusion hAK)
  have hsmul : ∀ (a : A) (k : K), ((a • k : K) : G) = (a : G) * k * (a : G)⁻¹ := fun _ _ => rfl
  have hnorm : ∀ U : Subgroup K, (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      A ≤ normalizer ((U.map K.subtype : Subgroup G) : Set G) := by
    intro U hU
    refine le_normalizer_of_conj_mem fun a ha g hg => ?_
    obtain ⟨u, hu, rfl⟩ := hg
    exact Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : A) • u, hU ⟨a, ha⟩ u hu, hsmul ⟨a, ha⟩ u⟩
  have hback : ∀ U : Subgroup G, A ≤ normalizer (U : Set G) →
      ∀ a : A, ∀ x ∈ U.subgroupOf K, a • x ∈ U.subgroupOf K := by
    intro U hAU a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAU a.2) x).mp hx
  have hprop : ∀ U : Subgroup K, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      ∀ x ∈ U, (x : G) ∈ M := by
    intro U hUt hU x hx
    have hlt : U.map K.subtype < K := by
      have := (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).mpr hUt
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    exact hproper _ hlt (hnorm U hU) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  let Kc : Subgroup K :=
    { carrier := {x | ∀ a : A, ((a • x : K) : G) ∈ M}
      mul_mem' := fun {x y} hx hy a => by
        rw [smul_mul', Subgroup.coe_mul]
        exact M.mul_mem (hx a) (hy a)
      one_mem' := fun a => by
        rw [smul_one]
        exact M.one_mem
      inv_mem' := fun {x} hx a => by
        rw [smul_inv', Subgroup.coe_inv]
        exact M.inv_mem (hx a) }
  have hKcinv : ∀ a : A, ∀ x ∈ Kc, a • x ∈ Kc := by
    intro a x hx b
    rw [← mul_smul]
    exact hx (b * a)
  have hKcM : ∀ x ∈ Kc, (x : G) ∈ M := fun x hx => by simpa using hx 1
  have hKclt : Kc < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hKM fun x hx => ?_
    exact hKcM ⟨x, hx⟩ (h ▸ Subgroup.mem_top _)
  have hUKc : ∀ U : Subgroup K, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U ≤ Kc :=
    fun U hUt hU x hx a => hprop U hUt hU _ (hU a x hx)
  have hnontriv : Nontrivial K := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro h
    exact hKM (h ▸ bot_le)
  obtain ⟨hfac, -⟩ := coprime_pgroup_commutator_factorization (A := A) (Q := K) hq hqK hqA
  have hD : actionCommutator A (⊤ : Subgroup K) = ⊤ := by
    by_contra hD
    have hDlt : actionCommutator A (⊤ : Subgroup K) < ⊤ := lt_top_iff_ne_top.mpr hD
    have hDinv : ∀ a : A, ∀ x ∈ actionCommutator A (⊤ : Subgroup K),
        a • x ∈ actionCommutator A (⊤ : Subgroup K) :=
      fun a x hx => smul_mem_actionCommutator_top hx a
    by_cases hfix : CFSG.fixedPointSubgroup A K = ⊤
    · refine hnc fun k hk g hg => ?_
      have h1 : (⟨k, hk⟩ : K) ∈ CFSG.fixedPointSubgroup A K := hfix ▸ Subgroup.mem_top _
      have h2 := congrArg Subtype.val (h1 ⟨g, hg⟩)
      rw [hsmul] at h2
      calc g * k = (g * k * g⁻¹) * g := by group
        _ = k * g := by rw [show g * k * g⁻¹ = k from h2]
    · have hfixlt : CFSG.fixedPointSubgroup A K < ⊤ := lt_top_iff_ne_top.mpr hfix
      have hfixinv : ∀ a : A, ∀ x ∈ CFSG.fixedPointSubgroup A K,
          a • x ∈ CFSG.fixedPointSubgroup A K := fun a x hx b => by
        rw [hx a]
        exact hx b
      refine hKM fun x hx => ?_
      obtain ⟨d, hd, c, hc, hdc⟩ := hfac ⟨x, hx⟩
      have hxM : ((⟨x, hx⟩ : K) : G) ∈ M := by
        rw [hdc, Subgroup.coe_mul]
        exact M.mul_mem (hKcM d (hUKc _ hDlt hDinv hd)) (hKcM c (hUKc _ hfixlt hfixinv hc))
      exact hxM
  obtain ⟨-, -, hfr, -⟩ := relative_minimal_action_frattini_irreducibility hq hqK hqA Kc hKclt
    hKcinv hD fun U hUt hU _ => hUKc U hUt hU
  refine ⟨?_, ?_, fun U hUK hAU => ?_⟩
  · have h := map_actionCommutator_conj hAK (⊤ : Subgroup K)
    rw [hD, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h.symm
  · have hΦ : frattini K < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => ?_
      have hbot : (⊥ : Subgroup K) = ⊤ := frattini_nongenerating (by rw [h, sup_top_eq])
      obtain ⟨x, hx⟩ := exists_ne (1 : K)
      exact hx (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_top x))
    have := (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).mpr hΦ
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  · have hlt : U.subgroupOf K < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => hUK.ne ?_
      refine le_antisymm hUK.le fun r hr => ?_
      have : (⟨r, hr⟩ : K) ∈ U.subgroupOf K := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    calc U = (U.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hUK.le).symm
      _ ≤ _ := Subgroup.map_mono (hfr _ hlt (hback U hAU))

theorem eq_one_of_acts_trivially_frattini_quotient {q : ℕ} (hq : q.Prime) {A K : Subgroup G}
    {z : G} (hqA : ¬ q ∣ Nat.card A) (hqK : IsPGroup q K) (hAK : A ≤ normalizer (K : Set G))
    (hzK : ¬ K ≤ centralizer ({z} : Set G))
    (hz : ∀ N : Subgroup G, N ≤ A → A ≤ normalizer (N : Set G) → N ≠ ⊥ → z ∈ N)
    {a : G} (haA : a ∈ A)
    (ha : ∀ k ∈ K, (a * k * a⁻¹)⁻¹ * k ∈ (frattini K).map K.subtype) : a = 1 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q K) := ⟨hqK⟩
  let _ : MulDistribMulAction A K := MulDistribMulAction.compHom K (Subgroup.inclusion hAK)
  have hsmul : ∀ (b : A) (k : K), ((b • k : K) : G) = (b : G) * k * (b : G)⁻¹ := fun _ _ => rfl
  have hΦinv : CFSG.IsInvariant A K (frattini K) :=
    CFSG.isInvariant_of_characteristic (A := A) (G := K) (frattini K)
  let _ : MulDistribMulAction A (K ⧸ frattini K) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := K) (frattini K) hΦinv
  have : MulAction.QuotientAction A (frattini K) :=
    CFSG.quotientAction_of_isInvariant (A := A) (frattini K) hΦinv
  obtain ⟨ρ, hρ⟩ : ∃ ρ : A →* MulAut (K ⧸ frattini K),
      ∀ (b : A) (v : K ⧸ frattini K), ρ b v = b • v :=
    ⟨MulDistribMulAction.toMulAut A (K ⧸ frattini K), fun _ _ => rfl⟩
  set C : Subgroup G := (ρ.ker).map A.subtype with hCdef
  have hCA : C ≤ A := map_subtype_le _
  have hAC : A ≤ normalizer (C : Set G) := by
    refine le_normalizer_of_conj_mem fun g hg x hx => ?_
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, ρ.normal_ker.conj_mem x' hx' ⟨g, hg⟩, ?_⟩
    simp
  by_contra ha1
  have haC : a ∈ C := by
    refine ⟨⟨a, haA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine MulEquiv.ext fun v => ?_
    refine QuotientGroup.induction_on v fun k => ?_
    rw [hρ]
    change (⟨a, haA⟩ : A) • (k : K ⧸ frattini K) = k
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    obtain ⟨y, hy, hyk⟩ := ha k.1 k.2
    have hyeq : y = ((⟨a, haA⟩ : A) • k)⁻¹ * k :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul]; exact hyk)
    rw [hyeq] at hy
    exact hy
  have hC : C ≠ ⊥ := by
    intro h
    exact ha1 (Subgroup.mem_bot.1 (h ▸ haC))
  obtain ⟨z', hz'ker, hz'⟩ := hz C hCA hAC hC
  set B : Subgroup A := Subgroup.zpowers z' with hBdef
  have hBker : B ≤ ρ.ker := zpowers_le.mpr hz'ker
  have hqB : ¬ q ∣ Nat.card B := fun h => hqA (h.trans (Subgroup.card_subgroup_dvd_card B))
  let _ : MulDistribMulAction B K := MulDistribMulAction.compHom K B.subtype
  have hΦinvB : CFSG.IsInvariant B K (frattini K) :=
    CFSG.isInvariant_of_characteristic (A := B) (G := K) (frattini K)
  have : MulAction.QuotientAction B (frattini K) :=
    CFSG.quotientAction_of_isInvariant (A := B) (frattini K) hΦinvB
  have hBsmul : ∀ (b : B) (k : K), b • k = (b : A) • k := fun _ _ => rfl
  have hquot :
      letI : MulDistribMulAction B (K ⧸ frattini K) :=
        CFSG.quotientMulDistribMulAction (A := B) (G := K) (frattini K)
          (CFSG.isInvariant_of_characteristic (A := B) (G := K) (frattini K))
      CFSG.ActsTrivially (A := B) (G := K ⧸ frattini K) := by
    intro b v
    refine QuotientGroup.induction_on v fun k => ?_
    have h1 : ρ (b : A) = 1 := hBker b.2
    have h2 := congrArg (fun φ : MulAut (K ⧸ frattini K) => φ (k : K ⧸ frattini K)) h1
    simp only [hρ, MulAut.one_apply] at h2
    rw [MulAction.Quotient.smul_coe] at h2
    change ((b • k : K) : K ⧸ frattini K) = k
    rw [hBsmul]
    exact h2
  have hfac := (coprime_pgroup_commutator_factorization (A := B) (Q := K) hq hqK hqB).1
  have hcomm_eq : CFSG.commutatorAction (A := B) (G := K) =
      actionCommutator B (⊤ : Subgroup K) := by
    unfold CFSG.commutatorAction CFSG.commutatorSubgroup actionCommutator
    congr 1
    ext x
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact ⟨h, hh, a, rfl⟩
    · rintro ⟨h, hh, a, rfl⟩
      exact ⟨a, h, hh, rfl⟩
  have hsup : CFSG.fixedPointSubgroup B K ⊔ CFSG.commutatorAction (A := B) (G := K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨d, hd, c, hc, rfl⟩ := hfac x
    exact Subgroup.mul_mem _ (mem_sup_right (hcomm_eq ▸ hd)) (mem_sup_left hc)
  have htriv := CFSG.actsTrivially_of_trivial_quotient_frattini_of_sup_eq_top (A := B) (R := K)
    (p := q) hsup hquot
  refine hzK fun k hk => ?_
  have h := congrArg Subtype.val (htriv ⟨z', Subgroup.mem_zpowers z'⟩ ⟨k, hk⟩)
  have hz'' : (z' : G) = z := hz'
  have h' : z * k * z⁻¹ = k := by
    rw [← hz'']
    exact h
  rw [mem_centralizer_singleton_iff]
  symm
  calc z * k = (z * k * z⁻¹) * z := by group
    _ = k * z := by rw [h']

theorem ExtremalObstruction.mem_of_normal_of_ne_bot (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : (P : Subgroup G) ≤ normalizer (D : Set G))
    {z : G} (hzZ : z ∈ (center D).map D.subtype) {N : Subgroup G}
    (hNA : N ≤ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)))
    (hAN : (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (N : Set G))
    (hN : N ≠ ⊥) : z ∈ N := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hD := (hext.exists_normal_plane hS hp hPD).1
  obtain ⟨-, hDP, -, -⟩ := hext.obstruction
  have hApG : IsPGroup p ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) : Subgroup G) :=
    P.isPGroup'.to_le inf_le_left
  have hAN' : (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ⊓ N ≠ ⊥ := by
    rwa [inf_eq_right.mpr hNA]
  obtain ⟨y, hyAN, hyc, hyo⟩ := exists_mem_inf_centralizer_of_ne_bot hApG hAN hAN'
  have hDA : D ≤ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) := le_inf hDP le_sup_left
  have hyP : y ∈ (P : Subgroup G) := hyAN.1.1
  have hyD : y ∈ centralizer (D : Set G) := centralizer_le (SetLike.coe_subset_coe.mpr hDA) hyc
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hyZ : y ∈ (center D).map D.subtype :=
    hext.mem_center_of_mem_centralizer hprime hodd hD hyP hyD hyp
  have hZc := hext.card_center_eq hprime hodd hD
  have hzy : zpowers y = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyZ) ?_
    rw [hZc, Nat.card_zpowers, hyo]
  exact (zpowers_le.mpr hyAN.2) (hzy ▸ hzZ)

@[expose] def SignalizerNoncentralIrreducible (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
        (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) →
        ¬ K ≤ centralizer ({z} : Set G) →
        ∀ q : ℕ, q.Prime → q ≠ p → IsPGroup q K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) → K' ≤ M) →
        ⁅K, (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))⁆ = K →
        (frattini K).map K.subtype < K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) →
          K' ≤ (frattini K).map K.subtype) →
        (∀ a ∈ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)),
          (∀ k ∈ K, (a * k * a⁻¹)⁻¹ * k ∈ (frattini K).map K.subtype) → a = 1) →
        ¬ (P : Subgroup G) ≤ normalizer (K : Set G) → K ≤ M

theorem signalizerNoncentralMinimal_of_irreducible (hS : Setting G)
    (h : SignalizerNoncentralIrreducible G) : SignalizerNoncentralMinimal G := by
  intro p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hPK
  by_contra hKM
  have hprime := sigmaA_prime p hp
  have hDP := hext.obstruction.2.1
  have hzA : z ∈ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) :=
    (le_inf hDP le_sup_left) (map_subtype_le _ hzZ)
  have hA : IsPGroup p ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) : Subgroup G) :=
    P.isPGroup'.to_le inf_le_left
  have hqA : ¬ q ∣ Nat.card ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) : Subgroup G) := by
    have : Fact p.Prime := ⟨hprime⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hA
    rw [hk]
    intro hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hprime).1 (hq.dvd_of_dvd_pow hdvd))
  have hnc : ¬ K ≤ centralizer (((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) :
      Subgroup G) : Set G) := fun hKc => hKz fun k hk =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hKc hk) z hzA).symm
  obtain ⟨hcomm, hΦ, hfr⟩ := frattini_irreducibility_of_minimal hq hqA hqK hAK hKM hnc hproper
  have hfaith : ∀ a ∈ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)),
      (∀ k ∈ K, (a * k * a⁻¹)⁻¹ * k ∈ (frattini K).map K.subtype) → a = 1 :=
    fun a haA ha => eq_one_of_acts_trivially_frattini_quotient hq hqA hqK hAK hKz
      (fun N hNA hAN hN => hext.mem_of_normal_of_ne_bot hS hp hPD hzZ hNA hAN hN) haA ha
  exact hKM (h p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr
    hfaith hPK)

theorem signalizerNoncentralPart_of_irreducible (hS : Setting G)
    (hI : SignalizerCentralNonConstrained G) (h : SignalizerNoncentralIrreducible G) :
    SignalizerNoncentralPart G :=
  signalizerNoncentralPart_of_minimal hS hI (signalizerNoncentralMinimal_of_irreducible hS h)

end CFSG.LocalAnalysis.RankThreeTheoremC
