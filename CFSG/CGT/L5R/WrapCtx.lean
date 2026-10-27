module

public import CFSG.CGT.L5R.Interfaces
public import CFSG.CGT.M24R.WrapCtx
public import CFSG.CGT.M24S.Balance
public import CFSG.CGT.M24S.NSHolt

public section

namespace CFSG.CGT.L5R

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Holt.General

variable {G : Type} [Group G]

theorem exists_mem_conjSubgroup_of_hyp [Finite G] [IsSimpleGroup G]
    (hHolt : CFSG.Holt.H78.HoltTheorem1) {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) :
    ∃ x g : G, x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ T ∧ x ∈ conjSubgroup g T := by
  by_contra hno
  have hNT := CFSG.CGT.M24R.normalizer_eq_of_centralizer_eq h hL hC
  obtain ⟨S, hTS, -, z, hzT, hz1, hZ⟩ := hL.sylow
  have hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
    ((hZ z (hTS hzT)).mpr (Or.inr rfl) s hs).symm
  have hz2 : z ^ 2 = 1 := h.wc.1.2 z hzT
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hconj : ∀ g : G, g⁻¹ * z * g ∈ H → g⁻¹ * z * g ∈ T := by
    intro g hg
    by_contra hgT
    refine hno ⟨g⁻¹ * z * g, g⁻¹, hNT ▸ hg, hgT, ?_⟩
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact hzT
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hTrip : IsHoltTriple G (G ⧸ H) z ((1 : G) : G ⧸ H) := by
    refine ⟨inferInstance, orderOf_eq_prime hz2 hz1, fun ω => ?_,
      ⟨S, hTS hzT, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq, mul_one,
      show (z * g)⁻¹ * g = g⁻¹ * z * g by rw [mul_inv_rev, hzinv], Subgroup.inv_mem_iff]
    refine ⟨fun hg => ?_, fun hg => H.mul_mem (H.mul_mem (H.inv_mem hg) (h.le hzT)) hg⟩
    have hzc : z ∈ conjSubgroup g T := mem_conjSubgroup.mpr (hconj g hg)
    have hne : T ⊓ conjSubgroup g T ≠ ⊥ := by
      intro hb
      have hz' : z ∈ T ⊓ conjSubgroup g T := Subgroup.mem_inf.mpr ⟨hzT, hzc⟩
      rw [hb, Subgroup.mem_bot] at hz'
      exact hz1 hz'
    rw [← hNT]
    exact mem_normalizer_of_conjSubgroup_eq (h.wc.conj_eq_of_inf_ne_bot hne)
  have hHtop : H ≠ ⊤ := by
    intro hH
    have : T.Normal := Subgroup.normalizer_eq_top_iff.mp (hNT.trans hH)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hb | ht
    · rw [hb, Subgroup.mem_bot] at hzT
      exact hz1 hzT
    · have h1 := hL.card_T
      have h2 := hL.card_H
      rw [ht, Subgroup.card_top] at h1
      rw [hH, Subgroup.card_top] at h2
      omega
  exact false_of_isHoltTriple hHolt hHtop (hL.card_sylow S) hZ hTrip

theorem sq_eq_one_of_mem_conjSubgroup {T : Subgroup G} (hT : IsWC T) {x g : G}
    (hxg : x ∈ conjSubgroup g T) : x ^ 2 = 1 := by
  have h2 := hT.1.2 _ (mem_conjSubgroup.1 hxg)
  have h3 : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by rw [sq, sq]; group
  rw [h3] at h2
  calc x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem card_inf_centralizer_eq_eight [Finite G] {T H : Subgroup G} (h : Hyp T H)
    (hL : LocalFacts T H) (hC : Subgroup.centralizer (T : Set G) = T) (h4 : ¬ HasType4 T) {x g : G}
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) (hxg : x ∈ conjSubgroup g T) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 8 := by
  have hle4 := four_le_card_inf_centralizer_of_sq_eq_one h.wc.1 hL.card_T hxN
    (sq_eq_one_of_mem_conjSubgroup h.wc hxg)
  have hdvd : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ∣ 16 :=
    hL.card_T ▸ Subgroup.card_dvd_of_le inf_le_left
  have h16 : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ≠ 16 := by
    intro h16
    have heq : T ⊓ Subgroup.centralizer ({x} : Set G) = T :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hL.card_T, h16])
    refine hxT (hC ▸ Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
    have htx := (heq.symm ▸ ht : t ∈ T ⊓ Subgroup.centralizer ({x} : Set G)).2
    exact Subgroup.mem_centralizer_singleton_iff.mp htx
  have h4' : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ≠ 4 := fun h' =>
    h4 ⟨x, g, hxN, hxT, hxg, h'⟩
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 4 from hdvd)
  rw [hm'] at hle4 h16 h4' ⊢
  interval_cases m <;> simp_all

theorem l52CtxHyp_conjSubgroup [Finite G] {T H : Subgroup G} (h : Hyp T H)
    (hL : LocalFacts T H) (hC : Subgroup.centralizer (T : Set G) = T)
    (hcompl : HasComplement T H) (h4 : ¬ HasType4 T) {x g : G}
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) (hxg : x ∈ conjSubgroup g T) :
    L52CtxHyp T (conjSubgroup g T) := by
  have hT := h.wc
  have hNT := CFSG.CGT.M24R.normalizer_eq_of_centralizer_eq h hL hC
  have hx1 : x ≠ 1 := fun hx => hxT (hx ▸ T.one_mem)
  have hne : conjSubgroup g T ≠ T := fun he => hxT (he ▸ hxg)
  have hwc₁ : IsWC (conjSubgroup g T) := hT.conj g
  have hle : T ⊓ Subgroup.centralizer ({x} : Set G) ≤ normIn T (conjSubgroup g T) :=
    fun t ht => mem_normIn.2 ⟨ht.1, hwc₁.centralizer_le_normalizer hxg hx1 ht.2⟩
  have hcx := card_inf_centralizer_eq_eight h hL hC h4 hxN hxT hxg
  have hLne : normIn T (conjSubgroup g T) ≠ ⊥ := by
    intro hb
    rw [hb, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hcx
    omega
  have c := Cfg.of_conj hT hne hLne
  have hxL₁ : x ∈ normIn (conjSubgroup g T) T := mem_normIn.2 ⟨hxg, hxN⟩
  have heq : T ⊓ Subgroup.centralizer ({x} : Set G) = normIn T (conjSubgroup g T) :=
    le_antisymm hle fun t ht => ⟨normIn_le _ _ ht,
      Subgroup.mem_centralizer_singleton_iff.2 (c.comm_L_L₁ ht hxL₁)⟩
  have hn1 : Nat.card (normIn T (conjSubgroup g T)) = 8 := by rw [← heq, hcx]
  exact
    { wc := hT
      card16 := hL.card_T
      inf_bot := hT.inf_conj_eq_bot hne
      conj := ⟨g, rfl⟩
      norm1 := hn1
      norm2 := by rw [← c.card_normIn_eq ⟨g, rfl⟩]; exact hn1
      cent_le := hL.centralizer_le
      cent_eq := hC
      trans := fun a ha ha1 b hb hb1 => by
        obtain ⟨k, hk, hkab⟩ := hL.transitive a ha ha1 b hb hb1
        exact ⟨k, hL.le_normalizer hk, hkab⟩
      quot := CFSG.CGT.M24R.nonempty_nQuot_equiv_alt8 h hNT
      compl := by
        obtain ⟨K, -, hTK, hTKH⟩ := hcompl
        exact ⟨K, by rw [inf_comm]; exact hTK, hTKH.trans hNT.symm⟩
      noType4 := h4 }

theorem exists_l52CtxHyp [Finite G] [IsSimpleGroup G] (hHolt : CFSG.Holt.H78.HoltTheorem1)
    {T H : Subgroup G} (h : Hyp T H) (hL : LocalFacts T H)
    (hC : Subgroup.centralizer (T : Set G) = T) (hcompl : HasComplement T H)
    (h4 : ¬ HasType4 T) : ∃ T₁ : Subgroup G, L52CtxHyp T T₁ := by
  obtain ⟨x, g, hxN, hxT, hxg⟩ := exists_mem_conjSubgroup_of_hyp hHolt h hL hC
  exact ⟨_, l52CtxHyp_conjSubgroup h hL hC hcompl h4 hxN hxT hxg⟩

end CFSG.CGT.L5R
