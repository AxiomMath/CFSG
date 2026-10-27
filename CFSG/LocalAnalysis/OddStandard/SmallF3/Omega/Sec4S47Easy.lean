module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FEven
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47K

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private abbrev sec4K0 (L A : Subgroup G) : Subgroup G :=
  (L ⊓ normalizer (A : Set G)) ⊔ oddCoreIn (centralizer (A : Set G))

private noncomputable abbrev sec4E (h : Sec4FSetup t L S z A B φ) : Subgroup G :=
  ((Equiv.Perm.sign.comp h.actHom).ker).map (normalizer (A : Set G)).subtype

private lemma Sec4FSetup.mem_E_iff (h : Sec4FSetup t L S z A B φ) {x : G}
    (hx : x ∈ normalizer (A : Set G)) :
    x ∈ sec4E h ↔ Equiv.Perm.sign (h.actHom ⟨x, hx⟩) = 1 :=
  ⟨fun ⟨y, hy, hyx⟩ => by obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hyx; exact hy,
    fun hs => ⟨⟨x, hx⟩, hs, rfl⟩⟩

private lemma Sec4FSetup.t_mem_E (h : Sec4FSetup t L S z A B φ) : t ∈ sec4E h :=
  (h.mem_E_iff (Subgroup.le_normalizer h.t_mem_A)).mpr (by
    rw [← h.eq_actHom (Subgroup.le_normalizer h.t_mem_A) (h.realizes_of_mem_A h.t_mem_A),
      map_one])

private lemma Sec4FSetup.mul_mem_E (h : Sec4FSetup t L S z A B φ) {b y : G}
    (hb : b ∈ normalizer (A : Set G)) (hy : y ∈ normalizer (A : Set G)) (hbE : b ∉ sec4E h)
    (hyE : y ∉ sec4E h) : b * y ∈ sec4E h := by
  rw [h.mem_E_iff hb] at hbE
  rw [h.mem_E_iff hy] at hyE
  refine (h.mem_E_iff (mul_mem hb hy)).mpr ?_
  change Equiv.Perm.sign (h.actHom (⟨b, hb⟩ * ⟨y, hy⟩)) = 1
  rw [map_mul, map_mul, (Int.units_eq_one_or _).resolve_left hbE,
    (Int.units_eq_one_or _).resolve_left hyE]
  decide

private lemma optionCongr_removeNone_of_fixed {α : Type*} [DecidableEq α]
    {σ : Equiv.Perm (Option α)} (h : σ none = none) :
    Equiv.optionCongr (Equiv.removeNone σ) = σ := by
  rw [map_equiv_removeNone, h, Equiv.swap_self]
  exact Equiv.trans_refl σ

private lemma Sec4FSetup.realizes_optionCongr (h : Sec4FSetup t L S z A B φ) {u : G} (huL : u ∈ L)
    {σ : Equiv.Perm (Fin 7)} (huv : ∀ v, IsEvenVec v → u * φ v * u⁻¹ = φ (permVec σ v)) :
    Sec4MRealizes t φ u (Equiv.optionCongr σ) := by
  intro p
  have hut : u * t * u⁻¹ = t := by rw [← h.t_cent_L huL, mul_inv_cancel_right]
  calc u * sec4MPt t φ p * u⁻¹ = (u * t * u⁻¹) * (u * φ (sec4MV p) * u⁻¹) := by
        rw [sec4MPt]; group
    _ = sec4MPt t φ (Equiv.optionCongr σ p) := by
        rw [hut, huv _ (sec4MV_even p), permVec_sec4MV]; rfl

private lemma Sec4FSetup.K0_le_X (h : Sec4FSetup t L S z A B φ) :
    sec4K0 L A ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) := by
  refine sup_le (fun u hu => ?_) fun o ho => ?_
  · obtain ⟨huL, huN⟩ := mem_inf.mp hu
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (h.t_cent_L huL).symm, huN⟩
  · have hoC : o ∈ centralizer (A : Set G) := (oddCoreIn_normal _).1 ho
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hoC t h.t_mem_A).symm,
      Subgroup.centralizer_le_normalizer (A : Set G) hoC⟩

private lemma Sec4FSetup.BO_le_K0 (h : Sec4FSetup t L S z A B φ) :
    B ⊔ oddCoreIn (centralizer (A : Set G)) ≤ sec4K0 L A :=
  sup_le_sup_right (fun _ hb => mem_inf.mpr ⟨h.B_le_L hb, Subgroup.le_normalizer (h.B_le_A hb)⟩) _

private lemma Sec4FSetup.K0_le_E (h : Sec4FSetup t L S z A B φ) : sec4K0 L A ≤ sec4E h := by
  refine sup_le (fun u hu => ?_) fun o ho => ?_
  · obtain ⟨huL, huN⟩ := mem_inf.mp hu
    have huB : u ∈ normalizer (B : Set G) := by
      have := inf_normalizer_le_normalizer_inf (H := A) (K := L)
        (mem_inf.mpr ⟨huN, Subgroup.le_normalizer huL⟩)
      rwa [h.data.B_eq] at this
    obtain ⟨σ, hσ, huv⟩ := h.data.bdata.perm.2.2.2.1 u ⟨huL, huB⟩
    refine (h.mem_E_iff huN).mpr ?_
    rw [← h.eq_actHom huN (h.realizes_optionCongr huL huv), Equiv.optionCongr_sign,
      Equiv.Perm.mem_alternatingGroup.mp hσ]
  · have hoC : o ∈ centralizer (A : Set G) := (oddCoreIn_normal _).1 ho
    have hoN := Subgroup.centralizer_le_normalizer (A : Set G) hoC
    refine (h.mem_E_iff hoN).mpr ?_
    rw [(h.actHom_eq_one_iff ⟨o, hoN⟩).mpr hoC, map_one]

private lemma Sec4FSetup.t_not_mem_K0 (h : Sec4FSetup t L S z A B φ) : t ∉ sec4K0 L A := by
  intro ht
  have hN : L ⊓ normalizer (A : Set G) ≤ normalizer (oddCoreIn (centralizer (A : Set G))) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm o ho
    exact h.conj_mem_oddCore (mem_inf.mp hm).2 ho
  obtain ⟨l, hl, o, ho, hlo⟩ : t ∈ ((L ⊓ normalizer (A : Set G) : Subgroup G) : Set G) *
      (oddCoreIn (centralizer (A : Set G)) : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hN]
    exact ht
  obtain ⟨k, hk⟩ := odd_orderOf_of_mem_oddCoreIn ho
  have hcomm : Commute t o :=
    mem_centralizer_iff.mp ((oddCoreIn_normal _).1 ho) t h.t_mem_A
  have hpow : l ^ (2 * k + 1) = t := by
    have ho1 : o⁻¹ ^ (2 * k + 1) = 1 := by rw [inv_pow, ← hk, pow_orderOf_eq_one, inv_one]
    rw [show l = t * o⁻¹ by rw [← hlo]; group, hcomm.inv_right.mul_pow, ho1, mul_one, pow_succ,
      pow_mul, pow_two, h.t_sq, one_pow, one_mul]
  exact sec4_t_not_mem h.ctx.toSec4Setting (hpow ▸ L.pow_mem (mem_inf.mp hl).1 (2 * k + 1))

private lemma Sec4FSetup.even_mem_K0_or_mul_t (h : Sec4FSetup t L S z A B φ) {x : G}
    (hx : x ∈ centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) (hxE : x ∈ sec4E h) :
    x ∈ sec4K0 L A ∨ x * t ∈ sec4K0 L A := by
  have hσ := optionCongr_removeNone_of_fixed ((h.actHom_none_iff ⟨x, hx.2⟩).mpr hx.1)
  have hτ : Equiv.removeNone (h.actHom ⟨x, hx.2⟩) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.optionCongr_sign, hσ]
    exact (h.mem_E_iff hx.2).mp hxE
  obtain ⟨u, ⟨huL, huB⟩, huv⟩ := h.data.bdata.perm.2.2.2.2 _ hτ
  have huN : u ∈ normalizer (A : Set G) := (h.normalizer_B_le ⟨huL, huB⟩).2
  have hcN : x * u⁻¹ ∈ normalizer (A : Set G) := mul_mem hx.2 (inv_mem huN)
  have hc : x * u⁻¹ ∈ centralizer (A : Set G) := (h.actHom_eq_one_iff ⟨_, hcN⟩).mp (by
    change h.actHom (⟨x, hx.2⟩ * (⟨u, huN⟩)⁻¹) = 1
    rw [map_mul, map_inv, ← h.eq_actHom huN (h.realizes_optionCongr huL huv), hσ,
      mul_inv_cancel])
  have huK : u ∈ sec4K0 L A := mem_sup_left (mem_inf.mpr ⟨huL, huN⟩)
  rcases h.cent_cases hc with hc | hc
  · exact Or.inl (by simpa using mul_mem (h.BO_le_K0 hc) huK)
  · refine Or.inr ?_
    have hxt : x * t = x * u⁻¹ * t * u := by rw [mul_assoc (x * u⁻¹), h.t_cent_L huL]; group
    rw [hxt]
    exact mul_mem (h.BO_le_K0 hc) huK

private lemma Sec4FSetup.index_two (h : Sec4FSetup t L S z A B φ) {K : Subgroup G}
    (hK0 : sec4K0 L A ≤ K) (hKX : K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G))
    (htK : t ∉ K)
    (hcov : ∀ b ∈ centralizer ({t} : Set G) ⊓ normalizer (A : Set G), ∃ y ∈ K, b * y ∈ sec4E h) :
    ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K := by
  refine ⟨K, hKX, relIndex_eq_two_iff_exists_notMem_and.mpr ⟨t, mem_inf.mpr
    ⟨mem_centralizer_singleton_iff.mpr rfl, Subgroup.le_normalizer h.t_mem_A⟩, htK,
      fun b hb => ?_⟩, htK⟩
  obtain ⟨y, hyK, hbyE⟩ := hcov b hb
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (mem_inf.mp (hKX hyK)).1
  rcases h.even_mem_K0_or_mul_t (mul_mem hb (hKX hyK)) hbyE with h1 | h1
  · exact Or.inr (by simpa using mul_mem (hK0 h1) (inv_mem hyK))
  · refine Or.inl ?_
    have hbt : b * t = b * y * t * y⁻¹ := by rw [mul_assoc b y t, hyt]; group
    rw [hbt]
    exact mul_mem (hK0 h1) (inv_mem hyK)

private lemma Sec4FSetup.mem_normalizer_K0 (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hyt : y ∈ centralizer ({t} : Set G)) :
    y ∈ normalizer (sec4K0 L A : Set G) := by
  refine inf_normalizer_le_normalizer_sup _ _ (mem_inf.mpr ⟨inf_normalizer_le_normalizer_inf
    (H := L) (K := normalizer (A : Set G)) (mem_inf.mpr ⟨h.cent_le_normalizer hyt,
      Subgroup.le_normalizer hyN⟩), ?_⟩)
  rw [mem_normalizer_iff]
  refine fun o => ⟨fun ho => h.conj_mem_oddCore hyN ho, fun ho => ?_⟩
  have h2 := h.conj_mem_oddCore (inv_mem hyN) ho
  rwa [show y⁻¹ * (y * o * y⁻¹) * y⁻¹⁻¹ = o by group] at h2

theorem Sec4FSetup.split47Cent_of_even (h : Sec4FSetup t L S z A B φ)
    (heven : ∀ (m : G) (hm : m ∈ normalizer (A : Set G)), m ∈ centralizer ({t} : Set G) →
      Equiv.Perm.sign (h.actHom ⟨m, hm⟩) = 1) :
    ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K :=
  h.index_two le_rfl h.K0_le_X h.t_not_mem_K0 fun b hb => ⟨1, one_mem _, by
    rw [mul_one]
    exact (h.mem_E_iff (mem_inf.mp hb).2).mpr (heven b _ (mem_inf.mp hb).1)⟩

theorem Sec4FSetup.split47Cent_of_odd_sq (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hyt : y ∈ centralizer ({t} : Set G))
    (hy2 : y * y ∈ (L ⊓ normalizer (A : Set G)) ⊔ oddCoreIn (centralizer (A : Set G)))
    (hodd : Equiv.Perm.sign (h.actHom ⟨y, hyN⟩) = -1) :
    ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K := by
  have hyE : y ∉ sec4E h := fun hy => by
    rw [h.mem_E_iff hyN, hodd] at hy
    exact absurd hy (by decide)
  refine h.index_two (K := sec4K0 L A ⊔ zpowers y) le_sup_left
    (sup_le h.K0_le_X (zpowers_le.mpr (mem_inf.mpr ⟨hyt, hyN⟩))) (fun ht => ?_) fun b hb => ?_
  · rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
      (zpowers_le.mpr (h.mem_normalizer_K0 hyN hyt))] at ht
    obtain ⟨k, hk, w, hw, hkw⟩ := ht
    replace hk : k ∈ sec4K0 L A := hk
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
    have hpow : ∀ i : ℤ, y ^ (2 * i) ∈ sec4K0 L A := fun i => by
      rw [zpow_mul, zpow_two]
      exact zpow_mem hy2 i
    obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
    · exact h.t_not_mem_K0 (hkw ▸ (sec4K0 L A).mul_mem hk (hpow i))
    · apply hyE
      have hy : y = (k * y ^ (2 * i))⁻¹ * t := by rw [← hkw, zpow_add_one]; group
      rw [hy]
      exact mul_mem (inv_mem (h.K0_le_E ((sec4K0 L A).mul_mem hk (hpow i)))) h.t_mem_E
  · by_cases hbE : b ∈ sec4E h
    · exact ⟨1, one_mem _, by rwa [mul_one]⟩
    · exact ⟨y, mem_sup_right (mem_zpowers y), h.mul_mem_E (mem_inf.mp hb).2 hyN hbE hyE⟩

theorem Sec4FSetup.split47Cent_of_odd_cent (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hyt : y ∈ centralizer ({t} : Set G)) (hy2 : y * y = 1)
    (hodd : Equiv.Perm.sign (h.actHom ⟨y, hyN⟩) = -1) :
    ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K :=
  h.split47Cent_of_odd_sq hyN hyt (by rw [hy2]; exact one_mem _) hodd

private lemma exists_fixed_of_sign_neg_one {σ : Equiv.Perm (Option (Fin 7))}
    (hσ2 : σ * σ = 1) (hsign : Equiv.Perm.sign σ = -1) : ∃ r, σ r = r := by
  by_contra h
  rw [not_exists] at h
  have hcard : Fintype.card (Function.fixedPoints σ) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun r => h r.1 r.2⟩
  have hsig := Equiv.Perm.sign_of_pow_two_eq_one (α := Option (Fin 7)) (by rwa [pow_two])
  rw [hcard, show Fintype.card (Option (Fin 7)) = 8 by simp, hsign,
    show (8 - 0) / 2 = (4 : ℕ) by norm_num, show (-1 : ℤˣ) ^ (4 : ℕ) = 1 by decide] at hsig
  exact absurd hsig (by decide)

theorem Sec4FSetup.split47Cent_of_odd_involution (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hy2 : y * y = 1)
    (hodd : Equiv.Perm.sign (h.actHom ⟨y, hyN⟩) = -1) :
    ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
      K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K := by
  obtain ⟨r, hr⟩ := exists_fixed_of_sign_neg_one
    (Sec4MRealizes.sq_eq_one h.pt_injective (h.actHom_spec ⟨y, hyN⟩) hy2) hodd
  obtain ⟨m, ν, hmN, -, -, hcomm, hνreal⟩ := h.exists_move_fixed (h.actHom_spec ⟨y, hyN⟩) hr
  have hy'N : m⁻¹ * y * m ∈ normalizer (A : Set G) := mul_mem (mul_mem (inv_mem hmN) hyN) hmN
  refine h.split47Cent_of_odd_cent hy'N (mem_centralizer_singleton_iff.mpr hcomm)
    (by rw [show m⁻¹ * y * m * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m by group, hy2]; group) ?_
  rw [← h.eq_actHom hy'N hνreal, map_mul, map_mul, map_inv, hodd, mul_right_comm,
    inv_mul_cancel, one_mul]

end CFSG.OddStandard.SmallF3.Omega
