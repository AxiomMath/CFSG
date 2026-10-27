module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Data
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

structure D2TransBorel (p : ℕ) {X : Type*} [Group X] (R : Sylow p X) (A X₀ K : Subgroup X)
    (z : X) : Prop where
  mem_A : z ∈ A
  orderOf_eq : orderOf z = p
  mem_K : z ∈ K
  center_eq :
    Subgroup.zpowers z = (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X)
  dichotomy : ∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ z ∈ W
  centralizer_le : X₀ ⊓ Subgroup.centralizer ({z} : Set X) ≤ R
  isSolvable : Group.IsSolvable X₀
  trans : ∃ b ∈ (R : Subgroup X), b * z * b⁻¹ = z ∧
    (∀ y ∈ A, b * y * b⁻¹ * y⁻¹ ∈ Subgroup.zpowers z) ∧
    ∃ a₀ ∈ A, ∀ k : ℕ, 0 < k → k < p → b ^ k * a₀ * (b ^ k)⁻¹ ≠ a₀
  exp : ∃ b ∈ (R : Subgroup X), b ^ p ≠ 1
  inv : ∃ t ∈ X₀, t ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
    ∃ e : ℕ, 6 ∣ e ∧ t ^ e * z * (t ^ e)⁻¹ = z⁻¹
  cyclic : ∀ T : Sylow p K, IsCyclic T

@[expose] def D2TransBorelAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → ∃ z : X, D2TransBorel p R A X₀ K z

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.exists_transData_of_borel [Fact p.Prime] (h : D2Escape p P M A H R)
    (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    {zb : H ⧸ primeComplementCore (G := H) p}
    (hB : D2TransBorel p Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K zb) :
    ∃ z : H, (z : G) ∈ A ∧ QuotientGroup.mk' (primeComplementCore (G := H) p) z = zb ∧
      D2TransData p M H R (Subgroup.zpowers (z : G)) A ∧
      Subgroup.zpowers (z : G) = R ⊓ Subgroup.centralizer (R : Set G) := by
  have hp : p.Prime := Fact.out
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπdef
  have hRH : R ≤ H := h.le_H
  have hAH : A ≤ H := h.A_le_H
  have hRp : IsPGroup p R := h.isPGroup
  obtain ⟨z, hzA, rfl⟩ := hB.mem_A
  have hzA' : (z : G) ∈ A := Subgroup.mem_subgroupOf.mp hzA
  have hzR : (z : G) ∈ R := h.A_le hzA'
  have himg : ((Subgroup.zpowers (z : G)).subgroupOf H).map π = Subgroup.zpowers (π z) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨z, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_zpowers _), rfl⟩)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have : y = z ^ n := Subtype.ext (by simpa using hn.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ n
  have hZp : IsPGroup p (Subgroup.zpowers (π z)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hB.orderOf_eq]
    exact ⟨1, (pow_one p).symm⟩
  have hZne : Subgroup.zpowers (π z) ≠ ⊥ := by
    intro hbot
    have h1 : orderOf (π z) = 1 := by
      rw [← Nat.card_zpowers, hbot, Subgroup.card_bot]
    rw [hB.orderOf_eq] at h1
    exact hp.one_lt.ne' h1
  have hD : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map π → ((H ⊓ M).subgroupOf H).map π ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) →
      W = ⊥ ∨ Subgroup.zpowers (π z) ≤ W := fun W hW hWn =>
    (hB.dichotomy W hW hWn).imp id fun hz => Subgroup.zpowers_le.mpr hz
  have hU := primeComplementCore_eq_bot_of_dichotomy hD hZp hZne
  have hpair : AGLPair p M H R :=
    h.toPair hglob (h.twoCore_inf_eq_of_primeCore_inf_eq (h.primeCore_inf_eq_iff.mpr hU))
  have hZR : Subgroup.zpowers (z : G) ≤ R := Subgroup.zpowers_le.mpr hzR
  have hcardZ : Nat.card (Subgroup.zpowers (z : G)) = p := by
    rw [← h.card_map_eq hZR, himg, Nat.card_zpowers, hB.orderOf_eq]
  have hlift : ∀ x w : H, (x : G) ∈ R → (w : G) ∈ R → π x = π w → (x : G) = w :=
    fun x w hx hw hxw => congrArg Subtype.val (eq_of_mk_eq_of_mem hRp hx hw hxw)
  have hπR : ∀ x : H, (x : G) ∈ R → π x ∈ (Rbar : Subgroup _) := fun x hx =>
    hRbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hcenter : Subgroup.zpowers (z : G) = R ⊓ Subgroup.centralizer (R : Set G) := by
    have hzC : π z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
      rw [← hB.center_eq]
      exact Subgroup.mem_zpowers _
    refine le_antisymm (Subgroup.zpowers_le.mpr ⟨hzR, Subgroup.mem_centralizer_iff.mpr
      fun r hr => ?_⟩) ?_
    · have hrH : r ∈ H := hRH hr
      have hc := Subgroup.mem_centralizer_iff.mp hzC.2 _ (hπR ⟨r, hrH⟩ hr)
      have := hlift (⟨r, hrH⟩ * z) (z * ⟨r, hrH⟩) (R.mul_mem hr hzR) (R.mul_mem hzR hr)
        (by rw [map_mul, map_mul, hc])
      simpa using this
    · rintro y ⟨hyR, hyC⟩
      have hyH : y ∈ H := hRH hyR
      have hmem : π ⟨y, hyH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
            Set (H ⧸ primeComplementCore (G := H) p)) := by
        refine ⟨hπR _ hyR, Subgroup.mem_centralizer_iff.mpr fun rb hrb => ?_⟩
        rw [hRbar] at hrb
        obtain ⟨r, hr, rfl⟩ := hrb
        have hc : (r : G) * y = y * r :=
          Subgroup.mem_centralizer_iff.mp hyC r (Subgroup.mem_subgroupOf.mp hr)
        rw [← map_mul, ← map_mul]
        exact congrArg π (Subtype.ext hc)
      rw [← hB.center_eq] at hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have := hlift (z ^ n) ⟨y, hyH⟩ (by simpa using R.zpow_mem hzR n) hyR (by rw [map_zpow, hn])
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using this⟩
  refine ⟨z, hzA', rfl, ⟨hpair, Subgroup.zpowers_le.mpr hzA', h.A_le, hcardZ, ?_, h.elem.2, ?_, ?_,
    ?_, ?_, fun L hL hLL => le_glbPrimeCore_of_perfect hB.isSolvable hL hLL⟩, hcenter⟩
  ·
    intro x hx y hy
    exact congrArg Subtype.val (h.elem.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  ·
    obtain ⟨bb, hbR, hbz, hbA, a0b, ha0, hmove⟩ := hB.trans
    rw [hRbar] at hbR
    obtain ⟨b, hb, rfl⟩ := hbR
    have hbR' : (b : G) ∈ R := Subgroup.mem_subgroupOf.mp hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha0
    have ha₀A : (a₀ : G) ∈ A := Subgroup.mem_subgroupOf.mp ha₀
    have hconjR : ∀ x : H, (x : G) ∈ R → ((b * x * b⁻¹ : H) : G) ∈ R := fun x hx =>
      R.mul_mem (R.mul_mem hbR' hx) (R.inv_mem hbR')
    refine ⟨b, hbR', fun x hx => ?_, fun y hy => ?_, a₀, ha₀A, fun k hk0 hkp hfix => ?_⟩
    ·
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hbz' : (b : G) * z * (b : G)⁻¹ = z :=
        hlift (b * z * b⁻¹) z (hconjR z hzR) hzR (by rw [map_mul, map_mul, map_inv, hbz])
      calc (b : G) * (z : G) ^ n * (b : G)⁻¹ = ((b : G) * z * (b : G)⁻¹) ^ n := by
            rw [conj_zpow]
        _ = (z : G) ^ n := by rw [hbz']
    ·
      have hyH : y ∈ H := hAH hy
      have hyR : y ∈ R := h.A_le hy
      have hmem := hbA (π ⟨y, hyH⟩) (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy))
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have heq : ((b * ⟨y, hyH⟩ * b⁻¹ * ⟨y, hyH⟩⁻¹ : H) : G) = ((z ^ n : H) : G) := by
        refine hlift _ _ (R.mul_mem (hconjR ⟨y, hyH⟩ hyR) (R.inv_mem hyR))
          (by simpa using R.zpow_mem hzR n) ?_
        rw [map_zpow, hn]
        simp only [map_mul, map_inv]
      rw [show (b : G) * y * (b : G)⁻¹ * y⁻¹ =
          ((b * ⟨y, hyH⟩ * b⁻¹ * ⟨y, hyH⟩⁻¹ : H) : G) by simp, heq]
      simp
    ·
      refine hmove k hk0 hkp ?_
      have hk : ((b ^ k * a₀ * (b ^ k)⁻¹ : H) : G) = (a₀ : G) := by simpa using hfix
      have := congrArg π (Subtype.ext hk : b ^ k * a₀ * (b ^ k)⁻¹ = a₀)
      simpa only [map_mul, map_inv, map_pow] using this
  ·
    obtain ⟨tb, htX₀, htN, e, he6, hinv⟩ := hB.inv
    obtain ⟨t, htM, htNR, rfl⟩ := h.exists_lift_normalizer htX₀ (hRbar ▸ htN)
    refine ⟨(t : G), ⟨t.2, htM⟩, e, he6, fun x hx => ?_⟩
    have hinvz : (t : G) ^ e * z * ((t : G) ^ e)⁻¹ = (z : G)⁻¹ := by
      have hmem : ((t ^ e * z * (t ^ e)⁻¹ : H) : G) ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htNR e) z).mp hzR
      have := hlift (t ^ e * z * (t ^ e)⁻¹) z⁻¹ hmem (by simpa using R.inv_mem hzR)
        (by rw [map_mul, map_mul, map_inv, map_pow, hinv, map_inv])
      simpa using this
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    calc (t : G) ^ e * (z : G) ^ n * ((t : G) ^ e)⁻¹ =
          ((t : G) ^ e * z * ((t : G) ^ e)⁻¹) ^ n := by rw [conj_zpow]
      _ = ((z : G) ^ n)⁻¹ := by rw [hinvz, inv_zpow]
  ·
    exact fun Y hY hYN => le_glbPrimeCore_or_le_of_forall h.primeCore_le (hZR.trans hRH)
      (hRp.to_le hZR) (fun W hW hWn => by rw [himg]; exact hD W hW hWn) hY hYN
  ·
    refine centralizer_le_of_map (X := Subgroup.zpowers (z : G)) ?_
    rw [himg, ← hRbar]
    exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (Subgroup.mem_zpowers _)))).trans hB.centralizer_le

end Escape

end CFSG.AGLEmbeddingD2
