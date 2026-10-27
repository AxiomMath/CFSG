module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3Sat
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientHyp
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups

namespace F3L57

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_le {A D C : Subgroup G} (hDC : D ≤ C)
    (h : (A.subgroupOf C).IsSubnormal) : (A.subgroupOf D).IsSubnormal := by
  have h1 := h.subgroupOf (K := D.subgroupOf C)
  have heq : A.subgroupOf D = ((A.subgroupOf C).subgroupOf (D.subgroupOf C)).comap
      (subgroupOfEquivOfLe hDC).symm.toMonoidHom := by
    ext x
    exact Iff.rfl
  rw [heq]
  exact h1.comap _

theorem le_normalizer_map_subtype {H : Subgroup G} (K : Subgroup ↥H) [K.Normal] :
    H ≤ normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, (inferInstance : K.Normal).conj_mem k hk _, rfl⟩
  · rintro ⟨k, hk, hkx⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩⁻¹⁻¹, (inferInstance : K.Normal).conj_mem k hk _, ?_⟩
    have h1 : (k : G) = h * x * h⁻¹ := hkx
    simp only [coe_subtype, coe_mul, coe_inv, inv_inv, h1]
    group

variable [Finite G]

theorem map_pPrimeCore_eq_inf {N A : Subgroup G} (hNA : N ≤ A)
    (hN : (N.subgroupOf A).IsSubnormal) :
    (pPrimeCore 2 ↥N).map N.subtype = N ⊓ (pPrimeCore 2 ↥A).map A.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ 2} hN
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore] at key
  let e : ↥(N.subgroupOf A) ≃* ↥N := subgroupOfEquivOfLe hNA
  have h1 : (pPrimeCore 2 ↥N).map N.subtype =
      ((pPrimeCore 2 ↥(N.subgroupOf A)).map (N.subgroupOf A).subtype).map A.subtype := by
    rw [← pPrimeCore_map_iso 2 e, map_map, map_map]
    rfl
  rw [h1, key, Subgroup.map_inf_eq _ _ A.subtype A.subtype_injective, subgroupOf_map_subtype,
    inf_eq_left.mpr hNA]

theorem map_pPrimeCore_le_of_normal {W H : Subgroup G} (hWH : W ≤ H)
    (hW : (W.subgroupOf H).Normal) :
    (pPrimeCore 2 ↥W).map W.subtype ≤ (pPrimeCore 2 ↥H).map H.subtype := by
  rw [map_pPrimeCore_eq_inf hWH hW.isSubnormal]
  exact inf_le_right

omit [Finite G] in
theorem odd_card_pPrimeCore (Y : Type*) [Group Y] [Finite Y] :
    Odd (Nat.card (pPrimeCore 2 Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

omit [Finite G] in
theorem le_pPrimeCore_of_normal {Y : Type*} [Group Y] {N : Subgroup Y} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ pPrimeCore 2 Y :=
  le_sSup ⟨hN, Nat.coprime_two_left.2 hodd⟩

omit [Finite G] in
theorem mem_oPrimeResidual_of_pow {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    x ∈ GH74.GLS.oPrimeResidual 2 G :=
  subset_closure ⟨k, hx⟩

omit [Finite G] in
theorem eq_one_of_pow_two_pow_of_mem {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : Odd (Nat.card N)) {x : Y} (hxN : x ∈ N) {k : ℕ} (hx : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hxN]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (Nat.card N) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem le_sup_of_isCyclic_sylow {W H D : Subgroup G} (hWH : W ≤ H)
    (hW : (W.subgroupOf H).Normal) (hcyc : ∀ S : Sylow 2 ↥W, IsCyclic S)
    (hD : ∀ x ∈ W, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ D) :
    W ≤ (pPrimeCore 2 ↥H).map H.subtype ⊔ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOW := map_pPrimeCore_le_of_normal hWH hW
  by_cases h2 : 2 ∣ Nat.card ↥W
  · have hmin : (Nat.card ↥W).minFac = 2 := (Nat.minFac_eq_two_iff _).2 h2
    let S : Sylow 2 ↥W := Classical.choice Sylow.nonempty
    have hc := IsCyclic.isComplement' hmin (hcyc S)
    set N := (MonoidHom.transferSylow S ((hcyc S).normalizer_le_centralizer hmin)).ker with hNdef
    have hNodd : ¬ 2 ∣ Nat.card N := MonoidHom.not_dvd_card_ker_transferSylow S _
    have hNO : N ≤ pPrimeCore 2 ↥W :=
      le_pPrimeCore_of_normal (MonoidHom.normal_ker _)
        (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hNodd))
    have htop : N ⊔ (S : Subgroup ↥W) = ⊤ := hc.sup_eq_top
    intro w hw
    have hw' : (⟨w, hw⟩ : ↥W) ∈ N ⊔ (S : Subgroup ↥W) := htop ▸ mem_top _
    have hmap : (N ⊔ (S : Subgroup ↥W)).map W.subtype ≤
        (pPrimeCore 2 ↥H).map H.subtype ⊔ D := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ((map_mono hNO).trans hOW) ?_
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := S.2 ⟨s, hs⟩
      refine hD _ s.2 k ?_
      have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
      simpa using congrArg Subtype.val hk'
    exact hmap ⟨⟨w, hw⟩, hw', rfl⟩
  · have hodd : Odd (Nat.card ↥W) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    have htop : (⊤ : Subgroup ↥W) ≤ pPrimeCore 2 ↥W :=
      le_pPrimeCore_of_normal normal_top (by rwa [card_top])
    intro w hw
    exact mem_sup_left (hOW ⟨⟨w, hw⟩, htop (mem_top _), rfl⟩)


theorem le_sup_pPrimeCore {p f : ℕ} (hp : p.Prime) (h3 : p ^ f = 3)
    (hcov : IsCoverOf .POmegaOdd 3 p f 2
      (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)))
    {z : G} (hz : orderOf z = 2) (hzX : z ∈ GH74.GLS.oPrimeResidual 2 G) :
    centralizer ({z} : Set G) ≤ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map
      (centralizer {z}).subtype ⊔ GH74.GLS.oPrimeResidual 2 G ⊓ centralizer {z} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := GH74.GLS.oPrimeResidual 2 G with hMdef
  have hMn : M.Normal := GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 G
  set H := centralizer ({z} : Set G) with hHdef
  set D := M ⊓ H with hDdef
  set OH := (pPrimeCore 2 ↥H).map H.subtype with hOHdef
  set ψ : G →* MulAut (↥M ⧸ pPrimeCore 2 ↥M) :=
    UnbalancingLocal.conjQuotAction M (pPrimeCore 2 ↥M) with hψ
  set z' : ↥M := ⟨z, hzX⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz
  have hOMo : Odd (Nat.card (pPrimeCore 2 ↥M)) := odd_card_pPrimeCore ↥M
  have hstep : ∀ h ∈ H, ∃ d ∈ D, d⁻¹ * h ∈ ψ.ker := by
    intro h hh
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    have hhm : h ^ m ∈ M := mem_oPrimeResidual_of_pow (k := a) (by
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
    have hinner : ψ h ^ m ∈ (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut _).range := by
      rw [← map_pow]
      exact ⟨_, (UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M)
        (⟨h ^ m, hhm⟩ : ↥M)).symm⟩
    obtain ⟨x, hx⟩ := mem_range_conj_of_pow_mem_three hp h3 hcov hm hinner
    obtain ⟨m₀, rfl⟩ := QuotientGroup.mk_surjective x
    have hhz : h * z * h⁻¹ = z := by
      rw [mem_centralizer_singleton_iff] at hh
      rw [hh, mul_inv_cancel_right]
    have hfix : MulAut.conj (m₀ : ↥M ⧸ pPrimeCore 2 ↥M) (z' : ↥M ⧸ pPrimeCore 2 ↥M) =
        (z' : ↥M ⧸ pPrimeCore 2 ↥M) := by
      rw [hx, hψ, UnbalancingLocal.conjQuotAction_mk' h z' (by
        show h * z * h⁻¹ ∈ M
        rw [hhz]
        exact hzX)]
      exact congrArg _ (Subtype.ext hhz)
    have hcen : QuotientGroup.mk' (pPrimeCore 2 ↥M) m₀ ∈
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥M) z'} : Set (↥M ⧸ pPrimeCore 2 ↥M)) := by
      rw [mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hfix
      exact hfix
    rw [← FooteLit.map_centralizer_mk'_of_odd hOMo hz'2] at hcen
    obtain ⟨d', hd', hd'm⟩ := hcen
    have hdH : (d' : G) ∈ H := by
      rw [hHdef, mem_centralizer_singleton_iff]
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hd'
      exact congrArg Subtype.val hd'
    refine ⟨d', ⟨d'.2, hdH⟩, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hx, hψ,
      UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M) d']
    have hdm : (d' : ↥M ⧸ pPrimeCore 2 ↥M) = (m₀ : ↥M ⧸ pPrimeCore 2 ↥M) := hd'm
    rw [hdm, inv_mul_cancel]
  set W := ψ.ker ⊓ H with hWdef
  have hWH : W ≤ H := inf_le_right
  have hWn : (W.subgroupOf H).Normal := by
    rw [hWdef, inf_subgroupOf_right]
    infer_instance
  have hcyc : ∀ S : Sylow 2 ↥W, IsCyclic S := by
    intro S
    set T : Subgroup G := (S : Subgroup ↥W).map W.subtype with hTdef
    have h2T : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨k, hk⟩ := S.2 ⟨s, hs⟩
      exact ⟨k, by simpa using congrArg (fun y : ↥(S : Subgroup ↥W) => ((y : ↥W) : G)) hk⟩
    have hTM : T ≤ M := fun t ht => by
      obtain ⟨k, hk⟩ := h2T t ht
      exact mem_oPrimeResidual_of_pow hk
    have hTk : T ≤ ψ.ker := by
      rintro _ ⟨s, -, rfl⟩
      exact (mem_inf.mp s.2).1
    let φ : ↥T →* ↥M ⧸ pPrimeCore 2 ↥M :=
      (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (Subgroup.inclusion hTM)
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro t ht
      rw [MonoidHom.mem_ker] at ht
      have h1 : Subgroup.inclusion hTM t ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp ht
      obtain ⟨k, hk⟩ := h2T t t.2
      have h2 : (Subgroup.inclusion hTM t) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      have h3' := eq_one_of_pow_two_pow_of_mem hOMo h1 h2
      rw [mem_bot]
      exact Subgroup.inclusion_injective hTM (h3'.trans (map_one _).symm)
    have hφZ : ∀ t : ↥T, φ t ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
      intro t
      have h1 : ψ (t : G) = 1 := hTk t.2
      have h2 := UnbalancingLocal.conjQuotAction_coe (Z := pPrimeCore 2 ↥M)
        (Subgroup.inclusion hTM t)
      rw [← hψ] at h2
      have h3' : ψ (t : G) = MulAut.conj (φ t) := h2
      rw [h1] at h3'
      rw [mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut (↥M ⧸ pPrimeCore 2 ↥M) => α g) h3'
      simp only [MulAut.one_apply, MulAut.conj_apply] at this
      rw [eq_mul_inv_iff_mul_eq] at this
      exact this
    have hcard : Nat.card T ≤ 2 := by
      rw [← hcov.2.1]
      exact Nat.card_le_card_of_injective (fun t => (⟨φ t, hφZ t⟩ : center _))
        (fun a b hab => hφinj (congrArg Subtype.val hab))
    have hScard : Nat.card S = Nat.card T :=
      (card_map_of_injective W.subtype_injective).symm
    have hpos : 0 < Nat.card S := Nat.card_pos
    rcases (show Nat.card S = 1 ∨ Nat.card S = 2 by omega) with h | h
    · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp h).1
      infer_instance
    · exact isCyclic_of_prime_card h
  have hW2 : ∀ x ∈ W, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ D := fun x hx k hk =>
    ⟨mem_oPrimeResidual_of_pow hk, hWH hx⟩
  have hWle := le_sup_of_isCyclic_sylow hWH hWn hcyc hW2
  intro h hh
  obtain ⟨d, hdD, hdk⟩ := hstep h hh
  have hw : d⁻¹ * h ∈ W := mem_inf.mpr ⟨hdk, mul_mem (inv_mem (mem_inf.mp hdD).2) hh⟩
  have h1 : h = d * (d⁻¹ * h) := by group
  rw [h1]
  exact mul_mem (mem_sup_right hdD) (hWle hw)

end F3L57

theorem harris82Lemma57SpinThree_holds : Harris82Lemma57SpinThree := by
  intro G _ _ _ p f hp h3 hcov z hz hzX _ J hJ _
  classical
  set M := GH74.GLS.oPrimeResidual 2 G with hMdef
  have hMn : M.Normal := GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 2 G
  set H := centralizer ({z} : Set G) with hHdef
  set OH := (pPrimeCore 2 ↥H).map H.subtype with hOHdef
  obtain ⟨hJH, hJs, hJO, hJiso⟩ := hJ
  have hOHJ : OH ≤ J := by
    rw [hOHdef, ← hJO]
    exact map_subtype_le _
  have hHD := F3L57.le_sup_pPrimeCore hp h3 hcov hz hzX
  set J₁ := J ⊓ M with hJ₁def
  have hJ₁D : J₁ ≤ M ⊓ H := le_inf inf_le_right (inf_le_left.trans hJH)
  have hDn : M ⊓ H ≤ normalizer (OH : Set G) :=
    inf_le_right.trans (F3L57.le_normalizer_map_subtype (pPrimeCore 2 ↥H))
  have hJeq : J = OH ⊔ J₁ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ ((M ⊓ H ⊔ OH : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hHD (hJH hx)
      rw [coe_mul_of_left_le_normalizer_right _ _ hDn] at hx'
      obtain ⟨d, hd, o, ho, rfl⟩ := hx'
      have hdJ : d ∈ J := by
        have h1 : d = d * o * o⁻¹ := by group
        rw [h1]
        exact mul_mem hx (inv_mem (hOHJ ho))
      rw [sup_comm]
      exact mul_mem_sup ⟨hdJ, hd.1⟩ ho
    · exact sup_le hOHJ inf_le_left
  have hJ₁J : (J₁.subgroupOf J).Normal := by
    rw [hJ₁def, inf_comm, inf_subgroupOf_right]
    infer_instance
  have hJ₁sH : (J₁.subgroupOf H).IsSubnormal := by
    have hJ₁J' : ((J₁.subgroupOf H).subgroupOf (J.subgroupOf H)).Normal := by
      have heq : (J₁.subgroupOf H).subgroupOf (J.subgroupOf H) =
          (J₁.subgroupOf J).comap (subgroupOfEquivOfLe hJH).toMonoidHom := by
        ext x
        exact Iff.rfl
      rw [heq]
      exact hJ₁J.comap _
    exact IsSubnormal.step _ _ (subgroupOf_mono H inf_le_left) hJs hJ₁J'
  have hJ₁s : (J₁.subgroupOf (M ⊓ H)).IsSubnormal :=
    F3L57.isSubnormal_subgroupOf_of_le inf_le_right hJ₁sH
  have hDH : ((M ⊓ H).subgroupOf H).Normal := by
    rw [inf_subgroupOf_right]
    infer_instance
  have hOD : (pPrimeCore 2 ↥(M ⊓ H)).map (M ⊓ H).subtype ≤ OH :=
    F3L57.map_pPrimeCore_le_of_normal inf_le_right hDH
  have hOJ₁ : (pPrimeCore 2 ↥J₁).map J₁.subtype = (pPrimeCore 2 ↥(M ⊓ H)).map (M ⊓ H).subtype := by
    rw [F3L57.map_pPrimeCore_eq_inf hJ₁D hJ₁s]
    refine inf_eq_right.mpr (le_inf (hOD.trans hOHJ) ?_)
    exact (map_subtype_le _).trans inf_le_left
  obtain ⟨-, -, -, ⟨esat⟩⟩ := F3.saturate (hJ₁D.trans inf_le_right) hJ₁sH
  have hsup : J₁ ⊔ OH = J := by rw [sup_comm, ← hJeq]
  let eJ : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥J₁ ⧸ pPrimeCore 2 ↥J₁ :=
    (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hsup).symm
      (pPrimeCore_map_iso 2 _)).trans esat
  have hJ₁iso : Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* PSL(2, ZMod 3)) ∨
      Nonempty (↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, ZMod 3)) := by
    rcases hJiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨eJ.symm.trans e⟩
    · exact Or.inr ⟨eJ.symm.trans e⟩
  have hO2 : GH74.GLS.oPrimeResidualOf 2 J = GH74.GLS.oPrimeResidualOf 2 J₁ := by
    simp only [GH74.GLS.oPrimeResidualOf, GH74.GLS.oPrimeResidual, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, coe_subtype]
    constructor
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      have hyM : (y : G) ∈ M := F3L57.mem_oPrimeResidual_of_pow (k := k) (by
        simpa using congrArg Subtype.val hk)
      exact ⟨⟨y, y.2, hyM⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
    · rintro ⟨y, ⟨k, hk⟩, rfl⟩
      exact ⟨⟨y, y.2.1⟩, ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩, rfl⟩
  exact ⟨J₁, ⟨hJ₁D, hJ₁s, hOJ₁, hJ₁iso⟩, hJeq, hO2⟩

end CFSG.ComponentClassification.HarrisLit.T1
