module

public import CFSG.LocalAnalysis.ABGTheoremB.V3Defs
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data

public section

namespace CFSG.ABGTheoremB

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G] [Finite G]

private theorem exists_invariant_complement_v3 {p : ℕ} (hp : p.Prime) {A K M : Subgroup G}
    (hA : IsPGroup 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hK : Odd (Nat.card K))
    (hMK : M ≤ K) (hM : IsPGroup p M) (hMidx : ¬ p ∣ M.relIndex K) :
    ∃ W : Subgroup G, W ≤ K ∧ A ≤ Subgroup.normalizer (W : Set G) ∧ ¬ p ∣ Nat.card W ∧
      W ⊓ M = ⊥ ∧ W ⊔ M = K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let π : Set Nat.Primes := {r | (r : ℕ) ≠ p}
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A K hAK
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hK)
  obtain ⟨H, hHall, hInv⟩ := CFSG.exists_isHallSubgroup_isInvariant hsolv hcop π
  have hWH : (H.map K.subtype).subgroupOf K = H := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hW : ¬ p ∣ Nat.card (H.map K.subtype) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    intro hdvd
    exact hHall.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hdvd rfl
  have hWM : H.map K.subtype ⊓ M = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hM
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hW).symm
  refine ⟨H.map K.subtype, Subgroup.map_subtype_le _, ?_, hW, hWM, ?_⟩
  · exact CFSG.SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A K hAK H
      (fun a x hx => (hInv.invariant a x).mp hx)
  · apply le_antisymm (sup_le (Subgroup.map_subtype_le _) hMK)
    rw [← Subgroup.relIndex_eq_one]
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro r hr hdvd
    have h1 : r ∣ H.index := by
      have := hdvd.trans (Subgroup.relIndex_dvd_of_le_left K
        (le_sup_left : H.map K.subtype ≤ H.map K.subtype ⊔ M))
      rwa [Subgroup.relIndex, hWH] at this
    have h2 : r ∣ M.relIndex K := hdvd.trans (Subgroup.relIndex_dvd_of_le_left K le_sup_right)
    have hrp : r = p := by
      by_contra hne
      exact hHall.p_in_pi_of_p_dvd_index ⟨r, hr⟩ h1 hne
    exact hMidx (hrp ▸ h2)

private theorem exists_conj_eq_of_complement_v3 {p : ℕ} (hp : p.Prime) {K M W₁ W₂ : Subgroup G}
    (hK : Odd (Nat.card K)) (hKM : K ≤ Subgroup.normalizer (M : Set G)) (hM : IsPGroup p M)
    (hW₁K : W₁ ≤ K) (hW₂K : W₂ ≤ K) (hW₁ : ¬ p ∣ Nat.card W₁) (hW₂ : ¬ p ∣ Nat.card W₂)
    (hW₁M : W₁ ⊔ M = K) (hW₂M : W₂ ⊔ M = K) :
    ∃ k ∈ K, W₂ = W₁.map (MulAut.conj k).toMonoidHom := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let π : Set Nat.Primes := {r | (r : ℕ) ≠ p}
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
  have hHall : ∀ W : Subgroup G, W ≤ K → ¬ p ∣ Nat.card W → W ⊔ M = K →
      CFSG.IsHallSubgroup π (W.subgroupOf K) := by
    intro W hWK hW hWM
    refine ⟨fun r hr hrp => ?_, fun r hr hrp => ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at hr
      exact hW (hrp ▸ hr)
    · apply hrp
      have h1 : W.relIndex K = W.relIndex M := by
        rw [← hWM, sup_comm]
        exact relIndex_sup_eq_relIndex_of_le_normalizer (hWK.trans hKM)
      have h2 : (r : ℕ) ∣ Nat.card M := by
        have := Subgroup.relIndex_mul_card W M
        exact (show (r : ℕ) ∣ W.relIndex M by rw [← h1]; exact hr).trans (Dvd.intro _ this)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hM
      rw [hk] at h2
      exact (Nat.prime_dvd_prime_iff_eq r.prop hp).mp (r.prop.dvd_of_dvd_pow h2)
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv
    (hHall W₁ hW₁K hW₁ hW₁M) (hHall W₂ hW₂K hW₂ hW₂M)
  refine ⟨g, g.2, ?_⟩
  have e₂ : (W₂.subgroupOf K).map K.subtype = W₂ := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hW₂K]
  rw [← e₂, hg, CFSG.map_subgroupOf_map_conj_eq hW₁K g]

private theorem coe_eq_mul_normalizer_of_complement_v3 {p : ℕ} (hp : p.Prime) {B K M W : Subgroup G}
    (hK : Odd (Nat.card K)) (hKB : K ≤ B) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hBM : B ≤ Subgroup.normalizer (M : Set G)) (hM : IsPGroup p M) (hWK : W ≤ K)
    (hW : ¬ p ∣ Nat.card W) (hWM : W ⊔ M = K) :
    (B : Set G) = (M : Set G) * ((B ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) := by
  have hMK : M ≤ K := hWM ▸ le_sup_right
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := hKB.trans hBM
  apply Set.Subset.antisymm
  · intro b hb
    have hKe : K.map (MulAut.conj b).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBK hb)
    have hMe : M.map (MulAut.conj b).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBM hb)
    have hinj : Function.Injective (MulAut.conj b).toMonoidHom := (MulAut.conj b).injective
    obtain ⟨k, hk, hkW⟩ := exists_conj_eq_of_complement_v3 hp hK hKM hM hWK
      (W₂ := W.map (MulAut.conj b).toMonoidHom) (hKe ▸ Subgroup.map_mono hWK) hW
      (by rwa [Subgroup.card_map_of_injective hinj]) hWM
      (by rw [← hMe, ← Subgroup.map_sup, hWM, hKe])
    have hk' : k ∈ ((M ⊔ W : Subgroup G) : Set G) := by
      rw [sup_comm, hWM]
      exact hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left M W (hWK.trans hKM)] at hk'
    obtain ⟨m, hm, w, hw, rfl⟩ := Set.mem_mul.mp hk'
    rw [show m * w = m * ((⟨w, Subgroup.le_normalizer hw⟩ : Subgroup.normalizer (W : Set G)) :
      G) from rfl, CFSG.map_conj_mul_right_eq_of_mem_normalizer] at hkW
    have hnorm : m⁻¹ * b ∈ Subgroup.normalizer (W : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
        CFSG.SolvableHall.map_conj_mul, hkW, ← CFSG.SolvableHall.map_conj_mul, inv_mul_cancel,
        CFSG.SolvableHall.map_conj_one]
    exact ⟨m, hm, m⁻¹ * b, ⟨B.mul_mem (B.inv_mem (hKB (hMK hm))) hb, hnorm⟩, by group⟩
  · rintro _ ⟨m, hm, n, hn, rfl⟩
    exact B.mul_mem (hKB (hMK hm)) hn.1

omit [Finite G] in
private theorem isCyclic_of_le_zpowers_sup_v3 {g : G} {M W : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (M : Set G)) (hWM : W ⊓ M = ⊥)
    (hW : W ≤ Subgroup.zpowers g ⊔ M) : IsCyclic W := by
  set A : Subgroup G := Subgroup.zpowers g ⊔ M with hA
  have hgA : g ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    sup_le ((Subgroup.zpowers_le).mpr hg) Subgroup.le_normalizer
  have hMA : M ≤ A := le_sup_right
  have : (M.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMA).mpr hAM
  have hcyc : IsCyclic (A ⧸ M.subgroupOf A) := by
    refine ⟨⟨(⟨g, hgA⟩ : A), ?_⟩⟩
    intro q
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have ha' : a ∈ ((Subgroup.zpowers g ⊔ M : Subgroup G) : Set G) := ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((Subgroup.zpowers_le).mpr hg)] at ha'
    obtain ⟨_, ⟨n, rfl⟩, m, hm, rfl⟩ := ha'
    refine ⟨n, ?_⟩
    change ((⟨g, hgA⟩ : A) : A ⧸ M.subgroupOf A) ^ n = _
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    change ((⟨g, hgA⟩ : A) ^ n)⁻¹ * ⟨_, ha⟩ ∈ M.subgroupOf A
    rw [Subgroup.mem_subgroupOf]
    simpa using hm
  let f : W →* A ⧸ M.subgroupOf A := (QuotientGroup.mk' _).comp (Subgroup.inclusion hW)
  refine isCyclic_of_injective f ((injective_iff_map_eq_one f).mpr fun w hw => ?_)
  have hwM : (w : G) ∈ M := by
    have := (QuotientGroup.eq_one_iff _).mp hw
    exact this
  have : (w : G) ∈ W ⊓ M := ⟨w.2, hwM⟩
  rw [hWM, Subgroup.mem_bot] at this
  exact Subtype.ext this

private theorem normalizer_le_normalizer_centralizer_v3 (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  apply Subgroup.mem_normalizer_fintype
  intro c hc
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro r hr
  have hrn : n⁻¹ * r * n ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hn)
      r).mp hr
    simpa using h
  have h := hc _ hrn
  calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * r := by group

private theorem normalizer_le_normalizer_oddCoreIn_v3 (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hle : (oddCoreIn H).map (MulAut.conj g).toMonoidHom ≤ oddCoreIn H := by
    apply le_oddCoreIn
    · exact (Subgroup.map_mono (oddCoreIn_le H)).trans hg.le
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact hg.ge.trans (Subgroup.map_mono (le_normalizer_oddCoreIn H))
    · rw [Subgroup.card_map_of_injective hinj]
      exact odd_card_oddCoreIn H
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hinj).ge

omit [Finite G] in
private theorem conj_mul_inv_mem_of_mem {O : Subgroup G} {a y u : G}
    (ha : a ∈ Subgroup.normalizer (O : Set G)) (hy : y ∈ Subgroup.normalizer (O : Set G))
    (hu : u ∈ O) (h : a * y * a⁻¹ * y⁻¹ ∈ O) : a * (y * u) * a⁻¹ * (y * u)⁻¹ ∈ O := by
  have hau : a * u * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp ha u).mp hu
  have h2 : y * (a * u * a⁻¹ * u⁻¹) * y⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp hy _).mp (O.mul_mem hau (O.inv_mem hu))
  have e : a * (y * u) * a⁻¹ * (y * u)⁻¹ =
      (a * y * a⁻¹ * y⁻¹) * (y * (a * u * a⁻¹ * u⁻¹) * y⁻¹) := by group
  rw [e]
  exact O.mul_mem h h2

omit [Finite G] in
private theorem conj_mul_mem_of_mem {O : Subgroup G} {a y u : G}
    (ha : a ∈ Subgroup.normalizer (O : Set G)) (hy : y ∈ Subgroup.normalizer (O : Set G))
    (hu : u ∈ O) (h : a * y * a⁻¹ * y ∈ O) : a * (y * u) * a⁻¹ * (y * u) ∈ O := by
  have hau : a * u * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp ha u).mp hu
  have h2 : y⁻¹ * (a * u * a⁻¹) * y⁻¹⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (O : Set G)).inv_mem hy) _).mp hau
  have e : a * (y * u) * a⁻¹ * (y * u) = (a * y * a⁻¹ * y) * (y⁻¹ * (a * u * a⁻¹) * y⁻¹⁻¹) * u := by
    group
  rw [e]
  exact O.mul_mem (O.mul_mem h h2) hu

omit [Finite G] in
private theorem mem_of_sq_mem_of_odd {H : Subgroup G} {x : G} (hx : Odd (orderOf x))
    (h : x ^ 2 ∈ H) : x ∈ H := by
  obtain ⟨m, hm⟩ := hx
  have e : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact H.pow_mem h _

omit [Finite G] in
private theorem relIndex_dvd_relIndex_of_le_v3 {H K L : Subgroup G} (hKL : K ≤ L)
    (hL : L ≤ Subgroup.normalizer (H : Set G)) : H.relIndex K ∣ H.relIndex L := by
  rw [← relIndex_sup_right_of_le_normalizer (hKL.trans hL),
    ← relIndex_sup_right_of_le_normalizer hL]
  exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex H (K ⊔ H) (L ⊔ H) le_sup_right
    (sup_le_sup_right hKL H))

omit [Finite G] in
private theorem le_of_isSylowOf_of_normalized_v3 {p : ℕ} [Fact p.Prime] {P K R : Subgroup G}
    (hP : IsSylowOf p P K) (hRK : R ≤ K) (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup p R) : R ≤ P := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have : (Subgroup.comap K.subtype R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mpr hKR
  have hle : R.subgroupOf K ≤ Q := IsPGroup.le_sylow_of_normal (hR.comap_subtype (K := K)) Q
  intro r hr
  have h : (⟨r, hRK hr⟩ : K) ∈ (Q : Subgroup K) := hle hr
  rw [hQ] at h
  exact h

omit [Finite G] in
private theorem coe_mul_coe_of_le_left_v3 {H L : Subgroup G} (h : H ≤ L) :
    (H : Set G) * (L : Set G) = L := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    exact L.mul_mem (h ha) hb
  · intro x hx
    exact Set.mem_mul.mpr ⟨1, H.one_mem, x, hx, one_mul x⟩

omit [Finite G] in
private theorem coe_mul_coe_of_le_right_v3 {H L : Subgroup G} (h : H ≤ L) :
    (L : Set G) * (H : Set G) = L := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    exact L.mul_mem ha (h hb)
  · intro x hx
    exact Set.mem_mul.mpr ⟨x, hx, 1, H.one_mem, mul_one x⟩

omit [Finite G] in
private theorem mem_of_pow_two_pow_mem_of_odd {H : Subgroup G} {x : G} (hx : Odd (orderOf x))
    (k : ℕ) (h : x ^ 2 ^ k ∈ H) : x ∈ H := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    apply mem_of_sq_mem_of_odd hx
    apply ih (hx.of_dvd_nat (orderOf_pow_dvd 2))
    rwa [← pow_mul, ← pow_succ']

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private structure V3Hyp (J : Subgroup G) : Prop where
  valid : σ.IsValid
  facts : σ.ChapterIIFacts
  le_L₀ : J ≤ σ.L₀
  pCore_le : pCoreIn σ.p σ.N ≤ J
  L₀_eq : σ.L₀ = J ⊔ σ.ON
  inf_ON : J ⊓ σ.ON = pCoreIn σ.p σ.N
  N_le_normalizer : σ.N ≤ Subgroup.normalizer (J : Set G)
  commutator_le : ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N
  quotient : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
    ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
      ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J

variable {σ} {J : Subgroup G}

omit [Finite G] in
private theorem isPGroup_pCoreIn_N : IsPGroup σ.p (pCoreIn σ.p σ.N) :=
  (CFSG.pCore_isPGroup (p := σ.p) (G := σ.N)).map σ.N.subtype

omit [Finite G] in
private theorem N_le_normalizer_pCoreIn : σ.N ≤ Subgroup.normalizer (pCoreIn σ.p σ.N : Set G) :=
  le_normalizer_map_subtype σ.N (CFSG.pCore σ.p σ.N)

omit [Finite G] in
private theorem isPGroup_D : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S

private theorem D_le_normalizer_C : σ.D ≤ Subgroup.normalizer (σ.C : Set G) :=
  inf_le_right.trans (normalizer_le_normalizer_centralizer_v3 σ.T)

private theorem D_le_normalizer_oddCoreIn_C : σ.D ≤ Subgroup.normalizer (oddCoreIn σ.C : Set G) :=
  D_le_normalizer_C.trans (normalizer_le_normalizer_oddCoreIn_v3 σ.C)

omit [Finite G] in
private theorem conj_mem_pCoreIn {g u : G} (hg : g ∈ σ.N) (hu : u ∈ pCoreIn σ.p σ.N) :
    g * u * g⁻¹ ∈ pCoreIn σ.p σ.N :=
  (Subgroup.mem_normalizer_iff.mp (N_le_normalizer_pCoreIn hg) u).mp hu

omit [Finite G] in
private theorem oddCoreIn_C_inf_le_N (σ : Setting G) (J : Subgroup G) :
    oddCoreIn σ.C ⊓ J ≤ σ.N :=
  inf_le_left.trans ((oddCoreIn_le σ.C).trans σ.C_le_N)

private abbrev kZero (σ : Setting G) (J : Subgroup G) : Subgroup G :=
  oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N

omit [Finite G] in
private theorem oddCoreIn_C_inf_L₀_le_N : oddCoreIn σ.C ⊓ σ.L₀ ≤ σ.N :=
  inf_le_left.trans ((oddCoreIn_le σ.C).trans σ.C_le_N)

omit [Finite G] in
private theorem coe_X_eq :
    ((oddCoreIn σ.C ⊓ σ.L₀ ⊔ σ.ON : Subgroup G) : Set G) =
      ((oddCoreIn σ.C ⊓ σ.L₀ : Subgroup G) : Set G) * (σ.ON : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (oddCoreIn_C_inf_L₀_le_N.trans σ.N_le_normalizer_ON)

private theorem C_inf_X_le_oddCoreIn_C :
    σ.C ⊓ (oddCoreIn σ.C ⊓ σ.L₀ ⊔ σ.ON) ≤ oddCoreIn σ.C := by
  have hON : σ.ON ⊓ σ.C ≤ oddCoreIn σ.C := by
    apply le_oddCoreIn inf_le_right
    · exact (le_inf (σ.C_le_N.trans σ.N_le_normalizer_ON) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  rintro x ⟨hxC, hxX⟩
  have hx' : x ∈ ((oddCoreIn σ.C ⊓ σ.L₀ ⊔ σ.ON : Subgroup G) : Set G) := hxX
  rw [coe_X_eq] at hx'
  obtain ⟨y, hy, u, hu, rfl⟩ := Set.mem_mul.mp hx'
  have huC : u ∈ σ.C := by
    have : u = y⁻¹ * (y * u) := by group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem (oddCoreIn_le σ.C hy.1)) hxC
  exact (oddCoreIn σ.C).mul_mem hy.1 (hON ⟨hu, huC⟩)

private theorem inv_mul_mem_centralizer_T (hII : σ.ChapterIIFacts) {d₁ d₂ : G}
    (hd₁ : d₁ ∈ σ.D) (hd₂ : d₂ ∈ σ.D) (hd₁' : d₁ ∉ Subgroup.centralizer (σ.T : Set G))
    (hd₂' : d₂ ∉ Subgroup.centralizer (σ.T : Set G)) :
    d₁⁻¹ * d₂ ∈ Subgroup.centralizer (σ.T : Set G) := by
  set Z := Subgroup.centralizer (σ.T : Set G)
  have h6 : Z.relIndex σ.D ∣ 6 := by
    rw [← hII.automizer_T]
    exact relIndex_dvd_relIndex_of_le_v3 inf_le_right
      (normalizer_le_normalizer_centralizer_v3 σ.T)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_D (σ := σ))
  have h2 : Z.relIndex σ.D ∣ 2 ^ k := hk ▸ Dvd.intro _ (Subgroup.relIndex_mul_card Z σ.D)
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hne : Z.relIndex σ.D ≠ 1 := fun h => hd₁' (Subgroup.relIndex_eq_one.mp h hd₁)
  have hidx : (Z.subgroupOf σ.D).index = 2 := by
    change Z.relIndex σ.D = 2
    rw [hjeq] at h6 hne ⊢
    rcases j with _ | _ | j
    · exact absurd (pow_zero 2) hne
    · rfl
    · exfalso
      have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ j + 2)).trans h6
      omega
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨d₁⁻¹, σ.D.inv_mem hd₁⟩)
    (b := ⟨d₂, hd₂⟩)).mpr
  simp only [Subgroup.mem_subgroupOf] at this
  exact this ⟨fun h => absurd (by simpa using Z.inv_mem h) hd₁', fun h => absurd h hd₂'⟩

private theorem forall_inverted (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h_centralized : ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
      ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, c * y * c⁻¹ * y⁻¹ ∈ σ.ON)
    (h_inverted : ∃ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) ∧
      ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, d * y * d⁻¹ * y ∈ σ.ON) :
    ∀ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) →
      ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, d * y * d⁻¹ * y ∈ σ.ON := by
  obtain ⟨d₀, hd₀, hd₀', hinv⟩ := h_inverted
  intro d hd hd' y hy
  set c := d₀⁻¹ * d with hc
  have hcC : c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G) :=
    ⟨σ.D.mul_mem (σ.D.inv_mem hd₀) hd, inv_mul_mem_centralizer_T hII hd₀ hd hd₀' hd'⟩
  have ho := h_centralized c hcC y hy
  have hd₀N : d₀ ∈ σ.N := σ.D_le_N hσ hd₀
  have h1 : d₀ * (c * y * c⁻¹ * y⁻¹) * d₀⁻¹ ∈ σ.ON :=
    (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON hd₀N) _).mp ho
  have e : d * y * d⁻¹ * y = (d₀ * (c * y * c⁻¹ * y⁻¹) * d₀⁻¹) * (d₀ * y * d₀⁻¹ * y) := by
    rw [hc]
    group
  rw [e]
  exact σ.ON.mul_mem h1 (hinv y hy)

omit [Finite G] in
private theorem le_kZero_of_mem {W : Subgroup G} (hW : W ∈ σ.familyW J) : W ≤ σ.kZero J :=
  le_sup_left.trans hW.2.2.2.le

omit [Finite G] in
private theorem conj_eq_of_mem {W : Subgroup G} (hW : W ∈ σ.familyW J) {c : G}
    (hc : c ∈ σ.N) (hcW : c ∈ Subgroup.normalizer (W : Set G))
    (hck : ∀ k ∈ oddCoreIn σ.C ⊓ J, c * k * c⁻¹ * k⁻¹ ∈ pCoreIn σ.p σ.N) {w : G} (hw : w ∈ W) :
    c * w * c⁻¹ = w := by
  have hwK : w ∈ ((oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N : Subgroup G) : Set G) :=
    le_kZero_of_mem hW hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((oddCoreIn_C_inf_le_N σ J).trans N_le_normalizer_pCoreIn)] at hwK
  obtain ⟨k, hk, u, hu, hku⟩ := Set.mem_mul.mp hwK
  have h1 : c * w * c⁻¹ * w⁻¹ ∈ pCoreIn σ.p σ.N := by
    rw [← hku]
    exact conj_mul_inv_mem_of_mem (N_le_normalizer_pCoreIn hc)
      (N_le_normalizer_pCoreIn ((oddCoreIn_C_inf_le_N σ J) hk)) hu (hck k hk)
  have h2 : c * w * c⁻¹ * w⁻¹ ∈ W :=
    W.mul_mem ((Subgroup.mem_normalizer_iff.mp hcW w).mp hw) (W.inv_mem hw)
  have h3 : c * w * c⁻¹ * w⁻¹ ∈ W ⊓ pCoreIn σ.p σ.N := ⟨h2, h1⟩
  rw [hW.2.2.1, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

omit [Finite G] in
private theorem conj_eq_inv_of_mem {W : Subgroup G} (hW : W ∈ σ.familyW J) {d : G}
    (hd : d ∈ σ.N) (hdW : d ∈ Subgroup.normalizer (W : Set G))
    (hdk : ∀ k ∈ oddCoreIn σ.C ⊓ J, d * k * d⁻¹ * k ∈ pCoreIn σ.p σ.N) {w : G} (hw : w ∈ W) :
    d * w * d⁻¹ = w⁻¹ := by
  have hwK : w ∈ ((oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N : Subgroup G) : Set G) :=
    le_kZero_of_mem hW hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((oddCoreIn_C_inf_le_N σ J).trans N_le_normalizer_pCoreIn)] at hwK
  obtain ⟨k, hk, u, hu, hku⟩ := Set.mem_mul.mp hwK
  have h1 : d * w * d⁻¹ * w ∈ pCoreIn σ.p σ.N := by
    rw [← hku]
    exact conj_mul_mem_of_mem (N_le_normalizer_pCoreIn hd)
      (N_le_normalizer_pCoreIn ((oddCoreIn_C_inf_le_N σ J) hk)) hu (hdk k hk)
  have h2 : d * w * d⁻¹ * w ∈ W := W.mul_mem ((Subgroup.mem_normalizer_iff.mp hdW w).mp hw) hw
  have h3 : d * w * d⁻¹ * w ∈ W ⊓ pCoreIn σ.p σ.N := ⟨h2, h1⟩
  rw [hW.2.2.1, Subgroup.mem_bot] at h3
  exact mul_eq_one_iff_eq_inv.mp h3

omit [Finite G] in
private theorem conj_inv_mem_pCoreIn {g u : G} (hg : g ∈ σ.N) (hu : u ∈ pCoreIn σ.p σ.N) :
    g⁻¹ * u * g ∈ pCoreIn σ.p σ.N := by
  simpa using conj_mem_pCoreIn (σ.N.inv_mem hg) hu

private theorem P_le_normalizer_Q (d : σ.IV7Data σ.p) :
    d.P ≤ Subgroup.normalizer (d.Q : Set G) := by
  have := d.Q_characteristic
  have h := le_normalizer_map_subtype d.P (d.Q.subgroupOf d.P)
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr d.Q_le] at h

private theorem D_le_normalizer_Q (d : σ.IV7Data σ.p) :
    σ.D ≤ Subgroup.normalizer (d.Q : Set G) := by
  have := d.Q_characteristic
  have h := d.P_D.trans (CFSG.SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic
    d.P (d.Q.subgroupOf d.P))
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr d.Q_le] at h

namespace V3Hyp

private theorem pCoreIn_le_ON (hJ : σ.V3Hyp J) : pCoreIn σ.p σ.N ≤ σ.ON := hJ.inf_ON ▸ inf_le_right

private theorem odd_card_pCoreIn (hJ : σ.V3Hyp J) : Odd (Nat.card (pCoreIn σ.p σ.N)) :=
  σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le hJ.pCoreIn_le_ON)

private theorem J_le_N (hJ : σ.V3Hyp J) : J ≤ σ.N := hJ.le_L₀.trans hJ.valid.L₀_le_N

private theorem kZero_le_J (hJ : σ.V3Hyp J) : σ.kZero J ≤ J := sup_le inf_le_right hJ.pCore_le

private theorem kZero_le_N (hJ : σ.V3Hyp J) : σ.kZero J ≤ σ.N := hJ.kZero_le_J.trans hJ.J_le_N

private theorem kZero_inf_ON (hJ : σ.V3Hyp J) : σ.kZero J ⊓ σ.ON = pCoreIn σ.p σ.N :=
  le_antisymm ((inf_le_inf_right _ hJ.kZero_le_J).trans hJ.inf_ON.le)
    (le_inf le_sup_right hJ.pCoreIn_le_ON)

private theorem odd_card_kZero (hJ : σ.V3Hyp J) : Odd (Nat.card (σ.kZero J)) := by
  rw [kZero, sup_comm]
  exact odd_card_sup_of_le_normalizer_of_odd
    ((oddCoreIn_C_inf_le_N σ J).trans N_le_normalizer_pCoreIn) hJ.odd_card_pCoreIn
    ((odd_card_oddCoreIn σ.C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

private theorem le_normalizer_kZero (hJ : σ.V3Hyp J) {A : Subgroup G} (hAN : A ≤ σ.N)
    (hAC : A ≤ Subgroup.normalizer (oddCoreIn σ.C : Set G)) :
    A ≤ Subgroup.normalizer (σ.kZero J : Set G) :=
  (le_inf ((le_inf hAC (hAN.trans hJ.N_le_normalizer)).trans
    Subgroup.inf_normalizer_le_normalizer_inf) (hAN.trans N_le_normalizer_pCoreIn)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem D_le_normalizer_kZero (hJ : σ.V3Hyp J) :
    σ.D ≤ Subgroup.normalizer (σ.kZero J : Set G) :=
  hJ.le_normalizer_kZero (σ.D_le_N hJ.valid) D_le_normalizer_oddCoreIn_C

private theorem C_le_normalizer_kZero (hJ : σ.V3Hyp J) :
    σ.C ≤ Subgroup.normalizer (σ.kZero J : Set G) :=
  hJ.le_normalizer_kZero σ.C_le_N (le_normalizer_oddCoreIn σ.C)

private theorem ON_le_normalizer_kZero (hJ : σ.V3Hyp J) :
    σ.ON ≤ Subgroup.normalizer (σ.kZero J : Set G) := by
  intro o ho
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hx' : x ∈ ((oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((oddCoreIn_C_inf_le_N σ J).trans N_le_normalizer_pCoreIn)] at hx'
  obtain ⟨k, hk, u, hu, rfl⟩ := Set.mem_mul.mp hx'
  have hc : ⁅k⁻¹, o⁆ ∈ pCoreIn σ.p σ.N :=
    hJ.commutator_le (Subgroup.commutator_mem_commutator (J.inv_mem hk.2) ho)
  have e : o * (k * u) * o⁻¹ = k * ⁅k⁻¹, o⁆ * (o * u * o⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [SetLike.mem_coe, e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem_sup hk hc)
    (Subgroup.mem_sup_right (conj_mem_pCoreIn (σ.ON_le_N ho) hu))

private theorem not_dvd_relIndex_kZero (hJ : σ.V3Hyp J)
    (h_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀)) :
    ¬ σ.p ∣ (pCoreIn σ.p σ.N).relIndex (σ.kZero J) := by
  have hX : σ.kZero J ≤ oddCoreIn σ.C ⊓ σ.L₀ ⊔ σ.ON :=
    sup_le (le_sup_of_le_left (inf_le_inf_left _ hJ.le_L₀))
      (le_sup_of_le_right hJ.pCoreIn_le_ON)
  have hXN : oddCoreIn σ.C ⊓ σ.L₀ ⊔ σ.ON ≤ Subgroup.normalizer (σ.ON : Set G) :=
    sup_le (inf_le_right.trans (hJ.valid.L₀_le_N.trans σ.N_le_normalizer_ON))
      Subgroup.le_normalizer
  have h1 : (pCoreIn σ.p σ.N).relIndex (σ.kZero J) = σ.ON.relIndex (σ.kZero J) := by
    rw [← Subgroup.inf_relIndex_right σ.ON, inf_comm, hJ.kZero_inf_ON]
  have h2 : σ.ON.relIndex (σ.kZero J) ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀) := by
    rw [← relIndex_sup_right_of_le_normalizer
      (inf_le_right.trans (hJ.valid.L₀_le_N.trans σ.N_le_normalizer_ON))]
    exact relIndex_dvd_relIndex_of_le_v3 hX hXN
  rw [h1]
  exact fun h => h_order (h.trans h2)

private theorem kZero_le_X (hJ : σ.V3Hyp J) : σ.kZero J ≤ oddCoreIn σ.C ⊓ σ.L₀ ⊔ σ.ON :=
  sup_le (le_sup_of_le_left (inf_le_inf_left _ hJ.le_L₀)) (le_sup_of_le_right hJ.pCoreIn_le_ON)

private theorem le_N_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    W ≤ σ.N :=
  hW.1.trans hJ.J_le_N

private theorem inf_ON_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    W ⊓ σ.ON = ⊥ := by
  rw [eq_bot_iff, ← hW.2.2.1]
  exact le_inf inf_le_left (hJ.inf_ON ▸ inf_le_inf_right σ.ON hW.1)

private theorem T_le_centralizer_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G}
    (hW : W ∈ σ.familyW J) : σ.T ≤ Subgroup.centralizer (W : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := conj_eq_of_mem hW (σ.T_le_N hJ.valid ht) (hW.2.1 (σ.T_le_D hJ.valid ht))
    (fun k hk => by
      have hkt : t * k = k * t := Subgroup.mem_centralizer_iff.mp (oddCoreIn_le σ.C hk.1) t ht
      rw [hkt, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _) hw
  calc w * t = t * w * t⁻¹ * t := by rw [h]
    _ = t * w := by group

private theorem le_C_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    W ≤ σ.C :=
  Subgroup.le_centralizer_iff.mp (hJ.T_le_centralizer_of_mem hW)

private theorem le_oddCoreIn_C_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G}
    (hW : W ∈ σ.familyW J) : W ≤ oddCoreIn σ.C := fun _ hw =>
  C_inf_X_le_oddCoreIn_C ⟨hJ.le_C_of_mem hW hw, hJ.kZero_le_X (le_kZero_of_mem hW hw)⟩

private theorem card_eq_relIndex_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G}
    (hW : W ∈ σ.familyW J) : Nat.card W = (pCoreIn σ.p σ.N).relIndex (σ.kZero J) := by
  change Nat.card W = (pCoreIn σ.p σ.N).relIndex (oddCoreIn σ.C ⊓ J ⊔ pCoreIn σ.p σ.N)
  rw [← hW.2.2.2, relIndex_sup_right_of_le_normalizer
    ((hJ.le_N_of_mem hW).trans N_le_normalizer_pCoreIn), ← Subgroup.inf_relIndex_right,
    inf_comm, hW.2.2.1, Subgroup.relIndex_bot_left]

private theorem kZero_inf_C_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    σ.kZero J ⊓ σ.C = W ⊔ σ.C ⊓ pCoreIn σ.p σ.N := by
  apply le_antisymm
  · rintro x ⟨hxK, hxC⟩
    have hx : x ∈ ((W ⊔ pCoreIn σ.p σ.N : Subgroup G) : Set G) := by
      rw [hW.2.2.2]
      exact hxK
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((hJ.le_N_of_mem hW).trans N_le_normalizer_pCoreIn)] at hx
    obtain ⟨w, hw, u, hu, rfl⟩ := Set.mem_mul.mp hx
    have huC : u ∈ σ.C := by
      have : u = w⁻¹ * (w * u) := by group
      rw [this]
      exact σ.C.mul_mem (σ.C.inv_mem (hJ.le_C_of_mem hW hw)) hxC
    exact Subgroup.mul_mem_sup hw ⟨huC, hu⟩
  · exact sup_le (le_inf (le_kZero_of_mem hW) (hJ.le_C_of_mem hW))
      (le_inf (inf_le_right.trans le_sup_right) inf_le_left)

private theorem mem_pCoreIn_of_mem (hJ : σ.V3Hyp J) {x : G} (hxJ : x ∈ J) (hxO : x ∈ σ.ON) :
    x ∈ pCoreIn σ.p σ.N :=
  hJ.inf_ON ▸ ⟨hxJ, hxO⟩

private theorem conj_mem_J (hJ : σ.V3Hyp J) {a k : G} (ha : a ∈ σ.N) (hk : k ∈ J) :
    a * k * a⁻¹ ∈ J :=
  (Subgroup.mem_normalizer_iff.mp (hJ.N_le_normalizer ha) k).mp hk

private theorem familyW_nonempty (hJ : σ.V3Hyp J)
    (h_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀)) : (σ.familyW J).Nonempty := by
  obtain ⟨W, hWK, hDW, -, hWP, hWPK⟩ := exists_invariant_complement_v3 hJ.valid.p_prime
    isPGroup_D hJ.D_le_normalizer_kZero hJ.odd_card_kZero
    (le_sup_right : pCoreIn σ.p σ.N ≤ σ.kZero J) isPGroup_pCoreIn_N
    (hJ.not_dvd_relIndex_kZero h_order)
  exact ⟨W, hWK.trans hJ.kZero_le_J, hDW, hWP, hWPK⟩

private theorem centralizer_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J)
    (h_centralized : ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, c * k * c⁻¹ * k⁻¹ ∈ σ.ON) :
    σ.D ⊓ Subgroup.centralizer (σ.T : Set G) ≤ Subgroup.centralizer (W : Set G) := by
  intro c hc
  have hcN : c ∈ σ.N := σ.D_le_N hJ.valid hc.1
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := conj_eq_of_mem hW hcN (hW.2.1 hc.1) (fun k hk => hJ.mem_pCoreIn_of_mem
    (J.mul_mem (hJ.conj_mem_J hcN hk.2) (J.inv_mem hk.2))
    (h_centralized c hc k ⟨hk.1, hJ.le_L₀ hk.2⟩)) hw
  calc w * c = c * w * c⁻¹ * c := by rw [h]
    _ = c * w := by group

private theorem inverted_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J)
    (h_inverted : ∀ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) →
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, d * k * d⁻¹ * k ∈ σ.ON) :
    ∀ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) → ∀ w ∈ W, d * w * d⁻¹ = w⁻¹ := by
  intro d hd hdT w hw
  have hdN : d ∈ σ.N := σ.D_le_N hJ.valid hd
  exact conj_eq_inv_of_mem hW hdN (hW.2.1 hd) (fun k hk => hJ.mem_pCoreIn_of_mem
    (J.mul_mem (hJ.conj_mem_J hdN hk.2) hk.2) (h_inverted d hd hdT k ⟨hk.1, hJ.le_L₀ hk.2⟩)) hw

omit [Finite G] in
private theorem C_le_normalizer_C_inf_pCoreIn :
    σ.C ≤ Subgroup.normalizer ((σ.C ⊓ pCoreIn σ.p σ.N : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer (σ.C_le_N.trans N_le_normalizer_pCoreIn)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem C_inf_pCoreIn_le (hJ : σ.V3Hyp J) {P : Subgroup G} (hP : IsSylowOf σ.p P σ.C) :
    σ.C ⊓ pCoreIn σ.p σ.N ≤ P :=
  have : Fact σ.p.Prime := ⟨hJ.valid.p_prime⟩
  le_of_isSylowOf_of_normalized_v3 hP inf_le_left C_le_normalizer_C_inf_pCoreIn
    isPGroup_pCoreIn_N.to_inf_right

private theorem le_sup_of_mem (hJ : σ.V3Hyp J) {W W₁ : Subgroup G} (hW : W ∈ σ.familyW J)
    (hW₁ : W₁ ∈ σ.familyW J) {P : Subgroup G} (hP : IsSylowOf σ.p P σ.C)
    (_hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) : W₁ ≤ W ⊔ P := by
  have h : W₁ ≤ σ.kZero J ⊓ σ.C := le_inf (le_kZero_of_mem hW₁) (hJ.le_C_of_mem hW₁)
  rw [hJ.kZero_inf_C_of_mem hW] at h
  exact h.trans (sup_le_sup_left (hJ.C_inf_pCoreIn_le hP) W)

private theorem kZero_le_C_sup_ON (hJ : σ.V3Hyp J) : σ.kZero J ≤ σ.C ⊔ σ.ON :=
  sup_le (le_sup_of_le_left (inf_le_left.trans (oddCoreIn_le σ.C)))
    (le_sup_of_le_right hJ.pCoreIn_le_ON)

private theorem C_sup_ON_eq_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J)
    (h_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀)) :
    ((σ.C ⊔ σ.ON : Subgroup G) : Set G) = (pCoreIn σ.p σ.N : Set G) *
      ((σ.C ⊔ σ.ON) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) :=
  coe_eq_mul_normalizer_of_complement_v3 hJ.valid.p_prime hJ.odd_card_kZero hJ.kZero_le_C_sup_ON
    (sup_le hJ.C_le_normalizer_kZero hJ.ON_le_normalizer_kZero)
    ((sup_le σ.C_le_N σ.ON_le_N).trans N_le_normalizer_pCoreIn) isPGroup_pCoreIn_N
    (le_kZero_of_mem hW)
    (by rw [hJ.card_eq_relIndex_of_mem hW]; exact hJ.not_dvd_relIndex_kZero h_order) hW.2.2.2

private theorem mul_comm_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J)
    {P₀ : Subgroup G} (hP₀ : IsSylowOf σ.p P₀ σ.C) : (W : Set G) * P₀ = P₀ * W := by
  set M : Subgroup G := σ.C ⊓ pCoreIn σ.p σ.N with hM
  have hMP : M ≤ P₀ := hJ.C_inf_pCoreIn_le hP₀
  have hWM : W ≤ Subgroup.normalizer (M : Set G) :=
    (hJ.le_C_of_mem hW).trans C_le_normalizer_C_inf_pCoreIn
  have hK₁ : P₀ ≤ Subgroup.normalizer ((W ⊔ M : Subgroup G) : Set G) := by
    rw [← hJ.kZero_inf_C_of_mem hW]
    exact (le_inf (hP₀.le.trans hJ.C_le_normalizer_kZero)
      (hP₀.le.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  calc (W : Set G) * P₀ = (W : Set G) * ((M : Set G) * P₀) := by
        rw [coe_mul_coe_of_le_left_v3 hMP]
    _ = ((W ⊔ M : Subgroup G) : Set G) * P₀ := by
        rw [← mul_assoc, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hWM]
    _ = ((W ⊔ M ⊔ P₀ : Subgroup G) : Set G) := by
        rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hK₁]
    _ = (P₀ : Set G) * ((W ⊔ M : Subgroup G) : Set G) := by
        rw [sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hK₁]
    _ = (P₀ : Set G) * ((M : Set G) * W) := by
        rw [sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hWM]
    _ = (P₀ : Set G) * W := by
        rw [← mul_assoc, coe_mul_coe_of_le_right_v3 hMP]

private theorem C_eq_of_mem (hJ : σ.V3Hyp J) {W : Subgroup G} (hW : W ∈ σ.familyW J)
    (h_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀)) :
    (σ.C : Set G) = ((σ.C ⊓ pCoreIn σ.p σ.N : Subgroup G) : Set G) *
      ((σ.C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G) := by
  have hK : σ.kZero J ⊓ σ.C = W ⊔ σ.C ⊓ pCoreIn σ.p σ.N := hJ.kZero_inf_C_of_mem hW
  refine coe_eq_mul_normalizer_of_complement_v3 hJ.valid.p_prime (K := W ⊔ σ.C ⊓ pCoreIn σ.p σ.N)
    ?_ ?_ ?_ C_le_normalizer_C_inf_pCoreIn isPGroup_pCoreIn_N.to_inf_right le_sup_left
    (by rw [hJ.card_eq_relIndex_of_mem hW]; exact hJ.not_dvd_relIndex_kZero h_order) rfl
  · rw [← hK]
    exact hJ.odd_card_kZero.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  · rw [← hK]
    exact inf_le_right
  · rw [← hK]
    exact (le_inf hJ.C_le_normalizer_kZero Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf

private theorem solvRadIn_L_le (hJ : σ.V3Hyp J) (hON : σ.ON ≠ ⊥) :
    solvRadIn σ.L ≤ σ.ON ⊔ centerOf σ.D := by
  have hσ := hJ.valid
  have hLN : σ.L ≤ σ.N := sup_le hσ.L₀_le_N (σ.S_le_N hσ)
  have hcov : (σ.L₀ : Set G) ⊆ (σ.L : Set G) * (σ.ON : Set G) := fun l hl =>
    Set.mem_mul.mpr ⟨l, (le_sup_left : σ.L₀ ≤ σ.L) hl, 1, σ.ON.one_mem, mul_one l⟩
  have hONL : σ.ON ≤ oddCoreIn σ.L :=
    le_oddCoreIn (hσ.ON_le_L₀.trans le_sup_left) (hLN.trans σ.N_le_normalizer_ON) σ.odd_card_ON
  have hO : oddCoreIn σ.L ≠ ⊥ := fun h => hON (le_bot_iff.mp (h ▸ hONL))
  rw [hJ.facts.qgroup_solvRad σ.L (σ.D_le_S.trans le_sup_right) hO hcov]
  have hOL : oddCoreIn σ.L ≤ σ.ON :=
    (le_inf le_rfl ((oddCoreIn_le σ.L).trans hLN)).trans
      (σ.oddCoreIn_inf_N_le_ON_of_cover hσ hJ.facts hcov)
  exact sup_le_sup_right hOL _

private theorem mem_J_of_mem_L₀ (hJ : σ.V3Hyp J) {d : G} (hd : d ∈ σ.L₀) {k : ℕ}
    (hdk : orderOf d = 2 ^ k) : d ∈ J := by
  have hd' : d ∈ ((J ⊔ σ.ON : Subgroup G) : Set G) := hJ.L₀_eq ▸ hd
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hJ.J_le_N.trans σ.N_le_normalizer_ON)] at hd'
  obtain ⟨j, hj, o, ho, rfl⟩ := Set.mem_mul.mp hd'
  have hjN : j ∈ σ.N := hJ.J_le_N hj
  have key : ∀ n : ℕ, (j * o) ^ n * (o ^ n)⁻¹ * (j ^ n)⁻¹ ∈ pCoreIn σ.p σ.N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : ⁅o ^ n, j⁆ ∈ pCoreIn σ.p σ.N := by
        apply hJ.commutator_le
        rw [← Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (σ.ON.pow_mem ho n) hj
      have e : (j * o) ^ (n + 1) * (o ^ (n + 1))⁻¹ * (j ^ (n + 1))⁻¹ =
          ((j * o) ^ n * (o ^ n)⁻¹ * (j ^ n)⁻¹) * (j ^ n * ⁅o ^ n, j⁆ * (j ^ n)⁻¹) := by
        rw [commutatorElement_def, pow_succ, pow_succ, pow_succ]
        group
      rw [e]
      exact Subgroup.mul_mem _ ih (conj_mem_pCoreIn (σ.N.pow_mem hjN n) hc)
  have h0 : (j * o) ^ 2 ^ k = 1 := hdk ▸ pow_orderOf_eq_one (j * o)
  have h1 := key (2 ^ k)
  rw [h0, one_mul] at h1
  have h2 : o ^ 2 ^ k ∈ J := by
    have e : o ^ 2 ^ k = (j ^ 2 ^ k)⁻¹ * ((o ^ 2 ^ k)⁻¹ * (j ^ 2 ^ k)⁻¹)⁻¹ := by group
    rw [e]
    exact J.mul_mem (J.inv_mem (J.pow_mem hj _)) (J.inv_mem (hJ.pCore_le h1))
  have h3 : o ^ 2 ^ k ∈ pCoreIn σ.p σ.N := hJ.mem_pCoreIn_of_mem h2 (σ.ON.pow_mem ho _)
  have hodd : Odd (orderOf o) :=
    σ.odd_card_ON.of_dvd_nat (Subgroup.orderOf_dvd_natCard σ.ON ho)
  exact J.mul_mem hj (hJ.pCore_le (mem_of_pow_two_pow_mem_of_odd hodd k h3))

private theorem exists_inverting_mem_J (hJ : σ.V3Hyp J)
    (h_centralized : ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
      ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, c * y * c⁻¹ * y⁻¹ ∈ σ.ON)
    (h_inverted : ∃ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) ∧
      ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, d * y * d⁻¹ * y ∈ σ.ON) :
    ∃ d ∈ σ.D, d ∈ J ∧ ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, d * y * d⁻¹ * y ∈ σ.ON := by
  have hσ := hJ.valid
  have hall := forall_inverted hσ hJ.facts h_centralized h_inverted
  obtain ⟨d₀, hd₀, hd₀T, -⟩ := h_inverted
  have hd₀L : d₀ ∈ ((σ.L₀ ⊔ σ.D ⊓ Subgroup.centralizer (σ.T : Set G) : Subgroup G) : Set G) := by
    rw [← hJ.facts.L_eq]
    exact (σ.D_le_S.trans (le_sup_right : (σ.S : Subgroup G) ≤ σ.L)) hd₀
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    ((inf_le_left.trans (σ.D_le_N hσ)).trans hσ.N_le_normalizer_L₀)] at hd₀L
  obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_mul.mp hd₀L
  have hlD : l ∈ σ.D := by
    have e : l = d₀ * c⁻¹ := by rw [← hlc]; group
    rw [e]
    exact σ.D.mul_mem hd₀ (σ.D.inv_mem hc.1)
  have hlT : l ∉ Subgroup.centralizer (σ.T : Set G) := fun h =>
    hd₀T (hlc ▸ Subgroup.mul_mem _ h hc.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (isPGroup_D (σ := σ)) ⟨l, hlD⟩
  exact ⟨l, hlD, hJ.mem_J_of_mem_L₀ hl ((Subgroup.orderOf_coe (⟨l, hlD⟩ : σ.D)).trans hk),
    hall l hlD hlT⟩

private theorem oddCoreIn_C_inf_J_le (hJ : σ.V3Hyp J) (hON : σ.ON ≠ ⊥) (dd : σ.IV7Data σ.p)
    {e : G} (heD : e ∈ σ.D) (heJ : e ∈ J)
    (he : ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, e * y * e⁻¹ * y ∈ σ.ON) :
    oddCoreIn σ.C ⊓ J ≤
      σ.C ⊓ Subgroup.normalizer (dd.Q : Set G) ⊔ σ.C ⊓ pCoreIn σ.p σ.N := by
  have hσ := hJ.valid
  set H₀ : Subgroup G := σ.C ⊓ Subgroup.normalizer (dd.Q : Set G) with hH₀
  have heN : e ∈ σ.N := σ.D_le_N hσ heD
  have heH₀ : e ∈ Subgroup.normalizer (H₀ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨D_le_normalizer_C heD, Subgroup.le_normalizer (D_le_normalizer_Q dd heD)⟩
  intro k hk
  have hkC : k ∈ σ.C := oddCoreIn_le σ.C hk.1
  have hkCL : k ∈ ((σ.C ⊓ σ.L : Subgroup G) : Set G) :=
    ⟨hkC, (le_sup_left : σ.L₀ ≤ σ.L) (hJ.le_L₀ hk.2)⟩
  obtain ⟨cs, hcs, s, hs, hcss⟩ := Set.mem_mul.mp (dd.Cstar_covers hkCL)
  have hs' : s ∈ ((σ.ON ⊔ centerOf σ.D : Subgroup G) : Set G) := hJ.solvRadIn_L_le hON hs.2
  have hZ : centerOf σ.D ≤ Subgroup.normalizer (σ.ON : Set G) :=
    inf_le_left.trans ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left σ.ON (centerOf σ.D) hZ] at hs'
  obtain ⟨o₁, ho₁, z, hz, hoz⟩ := Set.mem_mul.mp hs'
  have hzD : z ∈ σ.D := hz.1
  have hzN : z ∈ σ.N := σ.D_le_N hσ hzD
  have hzC : z ∈ σ.C := Subgroup.mem_centralizer_iff.mpr fun t ht =>
    Subgroup.mem_centralizer_iff.mp hz.2 t (σ.T_le_D hσ ht)
  have hyH₀ : cs * z ∈ H₀ :=
    ⟨σ.C.mul_mem hcs.1.1 hzC, Subgroup.mul_mem _ hcs.2 (D_le_normalizer_Q dd hzD)⟩
  have ho₁' : z⁻¹ * o₁ * z ∈ σ.ON := by
    have h := (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON (σ.N.inv_mem hzN)) o₁).mp ho₁
    rwa [inv_inv] at h
  set o := (z⁻¹ * o₁ * z)⁻¹ with ho
  set y := cs * z with hy
  have hoON : o ∈ σ.ON := σ.ON.inv_mem ho₁'
  have hyko : y = k * o := by
    rw [ho, hy, ← hcss, ← hoz]
    group
  have hoC : o ∈ σ.C := by
    have e1 : o = k⁻¹ * y := by rw [hyko]; group
    rw [e1]
    exact σ.C.mul_mem (σ.C.inv_mem hkC) hyH₀.1
  have ha : e * k * e⁻¹ * k ∈ pCoreIn σ.p σ.N :=
    hJ.mem_pCoreIn_of_mem (J.mul_mem (hJ.conj_mem_J heN hk.2) hk.2) (he k ⟨hk.1, hJ.le_L₀ hk.2⟩)
  have hb : ⁅e, o⁆ ∈ pCoreIn σ.p σ.N :=
    hJ.commutator_le (Subgroup.commutator_mem_commutator heJ hoON)
  have hc : ⁅k, o⁆ ∈ pCoreIn σ.p σ.N :=
    hJ.commutator_le (Subgroup.commutator_mem_commutator hk.2 hoON)
  have hkN : k ∈ σ.N := σ.C_le_N hkC
  have hoN : o ∈ σ.N := σ.ON_le_N hoON
  have ht : (y * (e * y * e⁻¹))⁻¹ * o ^ 2 ∈ pCoreIn σ.p σ.N := by
    have e1 : (y * (e * y * e⁻¹))⁻¹ * o ^ 2 =
        (o⁻¹ * ⁅e, o⁆⁻¹ * o) * (o⁻¹ * (k * (e * k * e⁻¹ * k)⁻¹ * k⁻¹) * o) *
          ((o * o)⁻¹ * ⁅k, o⁆⁻¹ * (o * o)) := by
      rw [hyko, commutatorElement_def, commutatorElement_def, pow_two]
      group
    rw [e1]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact conj_inv_mem_pCoreIn hoN (Subgroup.inv_mem _ hb)
    · exact conj_inv_mem_pCoreIn hoN (conj_mem_pCoreIn hkN (Subgroup.inv_mem _ ha))
    · exact conj_inv_mem_pCoreIn (σ.N.mul_mem hoN hoN) (Subgroup.inv_mem _ hc)
  have hyy : y * (e * y * e⁻¹) ∈ H₀ :=
    H₀.mul_mem hyH₀ ((Subgroup.mem_normalizer_iff.mp heH₀ y).mp hyH₀)
  have ho2 : o ^ 2 ∈ H₀ ⊔ σ.C ⊓ pCoreIn σ.p σ.N := by
    have e2 : o ^ 2 = (y * (e * y * e⁻¹)) * ((y * (e * y * e⁻¹))⁻¹ * o ^ 2) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hyy
      ⟨σ.C.mul_mem (σ.C.inv_mem hyy.1) (σ.C.pow_mem hoC 2), ht⟩
  have hoH : o ∈ H₀ ⊔ σ.C ⊓ pCoreIn σ.p σ.N :=
    mem_of_sq_mem_of_odd (σ.odd_card_ON.of_dvd_nat (Subgroup.orderOf_dvd_natCard σ.ON hoON)) ho2
  have e3 : k = y * o⁻¹ := by rw [hyko]; group
  rw [e3]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyH₀) (Subgroup.inv_mem _ hoH)

private theorem exists_mem_familyW_le_normalizer_Q (hJ : σ.V3Hyp J) (hON : σ.ON ≠ ⊥)
    (dd : σ.IV7Data σ.p) {e : G} (heD : e ∈ σ.D) (heJ : e ∈ J)
    (he : ∀ y ∈ oddCoreIn σ.C ⊓ σ.L₀, e * y * e⁻¹ * y ∈ σ.ON)
    (h_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀)) :
    ∃ W₁ ∈ σ.familyW J, W₁ ≤ Subgroup.normalizer (dd.Q : Set G) := by
  set H : Subgroup G := σ.kZero J ⊓ Subgroup.normalizer (dd.Q : Set G) with hH
  have hHN : H ≤ σ.N := inf_le_left.trans hJ.kZero_le_N
  have hHP : H ⊔ pCoreIn σ.p σ.N = σ.kZero J := by
    apply le_antisymm (sup_le inf_le_left le_sup_right)
    refine sup_le (fun k hk => ?_) le_sup_right
    have hk' : k ∈ ((σ.C ⊓ Subgroup.normalizer (dd.Q : Set G) ⊔ σ.C ⊓ pCoreIn σ.p σ.N :
        Subgroup G) : Set G) := hJ.oddCoreIn_C_inf_J_le hON dd heD heJ he hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_left.trans C_le_normalizer_C_inf_pCoreIn)] at hk'
    obtain ⟨h, hh, m, hm, rfl⟩ := Set.mem_mul.mp hk'
    have hhK : h ∈ σ.kZero J := by
      have e1 : h = (h * m) * m⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hm.2))
    exact Subgroup.mul_mem_sup ⟨hhK, hh.2⟩ hm.2
  have hDH : σ.D ≤ Subgroup.normalizer (H : Set G) :=
    (le_inf hJ.D_le_normalizer_kZero ((D_le_normalizer_Q dd).trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hidx : ¬ σ.p ∣ (pCoreIn σ.p σ.N ⊓ H).relIndex H := by
    rw [Subgroup.inf_relIndex_right,
      ← relIndex_sup_right_of_le_normalizer (hHN.trans N_le_normalizer_pCoreIn), hHP]
    exact hJ.not_dvd_relIndex_kZero h_order
  obtain ⟨W₁, hW₁H, hDW₁, -, hW₁M, hW₁MH⟩ := exists_invariant_complement_v3 hJ.valid.p_prime
    isPGroup_D hDH (hJ.odd_card_kZero.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    inf_le_right isPGroup_pCoreIn_N.to_inf_left hidx
  refine ⟨W₁, ⟨hW₁H.trans (inf_le_left.trans hJ.kZero_le_J), hDW₁, ?_, ?_⟩,
    hW₁H.trans inf_le_right⟩
  · rw [eq_bot_iff, ← hW₁M]
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hW₁H))
  · apply le_antisymm (sup_le (hW₁H.trans inf_le_left) le_sup_right)
    refine le_trans (le_of_eq hHP.symm) ?_
    rw [← hW₁MH]
    exact sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) le_sup_right

end V3Hyp

variable (σ)

theorem lemmaV31 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJL : J ≤ σ.L₀)
    (hpJ : pCoreIn σ.p σ.N ≤ J) (hL₀ : σ.L₀ = J ⊔ σ.ON) (hJO : J ⊓ σ.ON = pCoreIn σ.p σ.N)
    (hJn : σ.N ≤ Subgroup.normalizer (J : Set G)) (hJc : ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N)
    (hψ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
      ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
        ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J)
    (h_II_4_2_cyclic : ∃ g ∈ σ.N, oddCoreIn σ.C ⊓ σ.L₀ ≤ Subgroup.zpowers g ⊔ σ.ON)
    (h_II_4_2_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀))
    (h_II_4_2_centralized : ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, c * k * c⁻¹ * k⁻¹ ∈ σ.ON)
    (h_II_4_2_inverted : ∃ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) ∧
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, d * k * d⁻¹ * k ∈ σ.ON) :
    (σ.familyW J).Nonempty ∧ ∀ W ∈ σ.familyW J, IsCyclic W ∧ ¬ σ.p ∣ Nat.card W ∧
      Odd (Nat.card W) ∧ W ≤ oddCoreIn σ.C ∧ W ⊓ σ.ON = ⊥ ∧
      σ.D ⊓ Subgroup.centralizer (σ.T : Set G) ≤ Subgroup.centralizer (W : Set G) ∧
      ∀ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) → ∀ w ∈ W, d * w * d⁻¹ = w⁻¹ := by
  have hJ : σ.V3Hyp J := ⟨hσ, hII, hJL, hpJ, hL₀, hJO, hJn, hJc, hψ⟩
  refine ⟨hJ.familyW_nonempty h_II_4_2_order, fun W hW => ⟨?_, ?_, ?_, hJ.le_oddCoreIn_C_of_mem hW,
    hJ.inf_ON_of_mem hW, hJ.centralizer_of_mem hW h_II_4_2_centralized,
    hJ.inverted_of_mem hW (forall_inverted hσ hII h_II_4_2_centralized h_II_4_2_inverted)⟩⟩
  · obtain ⟨g, hgN, hX⟩ := h_II_4_2_cyclic
    exact isCyclic_of_le_zpowers_sup_v3 (σ.N_le_normalizer_ON hgN) (hJ.inf_ON_of_mem hW)
      ((le_kZero_of_mem hW).trans (hJ.kZero_le_X.trans (sup_le hX le_sup_right)))
  · rw [hJ.card_eq_relIndex_of_mem hW]
    exact hJ.not_dvd_relIndex_kZero h_II_4_2_order
  · exact (odd_card_oddCoreIn σ.C).of_dvd_nat
      (Subgroup.card_dvd_of_le (hJ.le_oddCoreIn_C_of_mem hW))

theorem lemmaV32 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJL : J ≤ σ.L₀)
    (hpJ : pCoreIn σ.p σ.N ≤ J) (hL₀ : σ.L₀ = J ⊔ σ.ON) (hJO : J ⊓ σ.ON = pCoreIn σ.p σ.N)
    (hJn : σ.N ≤ Subgroup.normalizer (J : Set G)) (hJc : ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N)
    (hψ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
      ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
        ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J)
    {W W₁ : Subgroup G} (hW : W ∈ σ.familyW J) (hW₁ : W₁ ∈ σ.familyW J) {P : Subgroup G}
    (hP : IsSylowOf σ.p P σ.C) (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) : W₁ ≤ W ⊔ P :=
  (V3Hyp.mk hσ hII hJL hpJ hL₀ hJO hJn hJc hψ).le_sup_of_mem hW hW₁ hP hPD

theorem lemmaV33 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJL : J ≤ σ.L₀)
    (hpJ : pCoreIn σ.p σ.N ≤ J) (hL₀ : σ.L₀ = J ⊔ σ.ON) (hJO : J ⊓ σ.ON = pCoreIn σ.p σ.N)
    (hJn : σ.N ≤ Subgroup.normalizer (J : Set G)) (hJc : ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N)
    (hψ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
      ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
        ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J)
    (h_II_4_2_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀))
    {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    W ⊓ σ.ON = ⊥ ∧
    (((σ.C ⊔ σ.ON : Subgroup G) : Set G) = (pCoreIn σ.p σ.N : Set G) *
      ((σ.C ⊔ σ.ON) ⊓ Subgroup.normalizer (W : Set G) : Subgroup G)) ∧
    (∀ P₀ : Subgroup G, IsSylowOf σ.p P₀ σ.C → (W : Set G) * P₀ = P₀ * W) ∧
    ((σ.C : Set G) = ((σ.C ⊓ pCoreIn σ.p σ.N : Subgroup G) : Set G) *
      ((σ.C ⊓ Subgroup.normalizer (W : Set G) : Subgroup G) : Set G)) := by
  have hJ : σ.V3Hyp J := ⟨hσ, hII, hJL, hpJ, hL₀, hJO, hJn, hJc, hψ⟩
  exact ⟨hJ.inf_ON_of_mem hW, hJ.C_sup_ON_eq_of_mem hW h_II_4_2_order,
    fun _ hP₀ => hJ.mul_comm_of_mem hW hP₀, hJ.C_eq_of_mem hW h_II_4_2_order⟩

theorem lemmaV33v (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJL : J ≤ σ.L₀)
    (hpJ : pCoreIn σ.p σ.N ≤ J) (hL₀ : σ.L₀ = J ⊔ σ.ON) (hJO : J ⊓ σ.ON = pCoreIn σ.p σ.N)
    (hJn : σ.N ≤ Subgroup.normalizer (J : Set G)) (hJc : ⁅J, σ.ON⁆ ≤ pCoreIn σ.p σ.N)
    (hψ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = σ.q ∧
      ∃ ψ : J →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective ψ ∧
        ψ.ker = (pCoreIn σ.p σ.N).subgroupOf J)
    (h_II_4_2_order : ¬ σ.p ∣ σ.ON.relIndex (oddCoreIn σ.C ⊓ σ.L₀))
    (h_II_4_2_centralized : ∀ c ∈ σ.D ⊓ Subgroup.centralizer (σ.T : Set G),
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, c * k * c⁻¹ * k⁻¹ ∈ σ.ON)
    (h_II_4_2_inverted : ∃ d ∈ σ.D, d ∉ Subgroup.centralizer (σ.T : Set G) ∧
      ∀ k ∈ oddCoreIn σ.C ⊓ σ.L₀, d * k * d⁻¹ * k ∈ σ.ON)
    (hr : σ.HypIV7 σ.p) (d : σ.IV7Data σ.p) {W : Subgroup G} (hW : W ∈ σ.familyW J) :
    W ≤ Subgroup.normalizer (d.Q : Set G) := by
  have hJ : σ.V3Hyp J := ⟨hσ, hII, hJL, hpJ, hL₀, hJO, hJn, hJc, hψ⟩
  have hON : σ.ON ≠ ⊥ := by
    intro h
    have h' := hr.dvd_ON
    rw [h, Subgroup.card_bot] at h'
    exact hr.prime.not_dvd_one h'
  obtain ⟨e, heD, heJ, he⟩ := hJ.exists_inverting_mem_J h_II_4_2_centralized h_II_4_2_inverted
  obtain ⟨W₁, hW₁, hW₁Q⟩ :=
    hJ.exists_mem_familyW_le_normalizer_Q hON d heD heJ he h_II_4_2_order
  exact (hJ.le_sup_of_mem hW₁ hW d.P_sylow d.P_D).trans (sup_le hW₁Q (P_le_normalizer_Q d))

end Setting

end CFSG.ABGTheoremB

end
