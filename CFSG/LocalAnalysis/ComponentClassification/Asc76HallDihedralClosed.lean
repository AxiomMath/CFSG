module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76HallDihedralBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Dihedral
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D13

public section

namespace CFSG.ComponentClassification.Asc76X.HallDihedral

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.Asc76 CFSG.ComponentClassification.Asc76.Sec4
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G]

@[expose] def IsSq (U : Subgroup G) (u : G) : Prop :=
  ∃ v ∈ U, v * v = u

omit [Finite G] in
theorem isSq_zpow_of_even {U : Subgroup G} {ρ : G} (hρ : zpowers ρ = U) {i : ℤ} (hi : Even i) :
    IsSq U (ρ ^ i) := by
  obtain ⟨m, rfl⟩ := hi
  exact ⟨ρ ^ m, hρ ▸ zpow_mem (mem_zpowers ρ) m, (zpow_add ρ m m).symm⟩

namespace IsSq

variable {U R : Subgroup G}

omit [Finite G] in
theorem mul_of_not (hU : IsDihedralRot U R) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (hna : ¬ IsSq U a) (hnb : ¬ IsSq U b) : IsSq U (a * b) := by
  obtain ⟨ρ, hρ, -⟩ := hU.exists_gen
  rw [← hρ] at ha hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  have hi : Odd i := Int.not_even_iff_odd.mp fun he => hna (isSq_zpow_of_even hρ he)
  have hj : Odd j := Int.not_even_iff_odd.mp fun he => hnb (isSq_zpow_of_even hρ he)
  rw [← zpow_add]
  exact isSq_zpow_of_even hρ (hi.add_odd hj)

omit [Finite G] in
theorem mul (hU : IsDihedralRot U R) {a b : G} (ha : IsSq U a) (hb : IsSq U b) :
    IsSq U (a * b) := by
  obtain ⟨v, hv, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  refine ⟨v * w, mul_mem hv hw, ?_⟩
  have hc : w * v = v * w := hU.commute_of_mem hw hv
  calc v * w * (v * w) = v * (w * v) * w := by group
    _ = v * (v * w) * w := by rw [hc]
    _ = v * v * (w * w) := by group

omit [Finite G] in
theorem not_inv {a : G} (hna : ¬ IsSq U a) : ¬ IsSq U a⁻¹ := by
  rintro ⟨v, hv, hva⟩
  apply hna
  refine ⟨v⁻¹, inv_mem hv, ?_⟩
  rw [← mul_inv_rev, hva, inv_inv]

omit [Finite G] in
theorem one : IsSq U 1 := ⟨1, U.one_mem, mul_one 1⟩

end IsSq

omit [Finite G] in
theorem eq_of_mem_zpowers {s y : G} (hss : s * s = 1) (hy : y ∈ zpowers s) : y = 1 ∨ y = s := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hs2 : s ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hss
  have hk := Int.emod_two_eq_zero_or_one k
  have e : s ^ k = s ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, hs2, one_zpow, mul_one]
  rcases hk with hk | hk
  · left
    rw [e, hk, zpow_zero]
  · right
    rw [e, hk, zpow_one]

namespace Hyp

variable {Ω : Set (Subgroup G)} {S K R U : Subgroup G} {t z : G}

theorem isSq_z (h : Hyp Ω S K R U t z) : IsSq U z := by
  obtain ⟨v, hv, e⟩ := h.rot.exists_sq_of_mul_self h.z_mem h.z_mul
  exact ⟨v, hv, e.symm⟩

namespace Outer

variable {x : G}

theorem not_sq (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) {r : G} (hrR : r ∈ R)
    (hrU : r ∉ U) : r⁻¹ * (x * r * x⁻¹) ∈ U ∧ ¬ IsSq U (r⁻¹ * (x * r * x⁻¹)) := by
  have hxR : x * r * x⁻¹ ∈ R := (mem_normalizer_iff.mp (h.le_normalizer_R hx.mem) r).mp hrR
  have hxU : x * r * x⁻¹ ∉ U := fun hU => hrU (by
    have h1 := (mem_normalizer_iff.mp (h.le_normalizer_U hx.mem) r).mpr hU
    exact h1)
  have hrr : r * r = 1 := h.rot.mul_self r hrR hrU
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hmem : r⁻¹ * (x * r * x⁻¹) ∈ U := by
    rw [hrinv]
    exact h.rot.mul_mem_of_not_mem hrR hxR hrU hxU
  refine ⟨hmem, ?_⟩
  rintro ⟨v, hv, hvu⟩
  have hxv : x * v * x⁻¹ = v⁻¹ := hx.inv h v hv
  have hcomm : x * (r * v) = r * v * x := by
    have e1 : x * r * x⁻¹ = r * (v * v) := by
      rw [hvu]
      group
    calc x * (r * v) = (x * r * x⁻¹) * (x * v * x⁻¹) * x := by group
      _ = r * (v * v) * v⁻¹ * x := by rw [e1, hxv]
      _ = r * v * x := by group
  have hrvR : r * v ∈ R := mul_mem hrR (h.rot.le hv)
  have hrvU : r * v ∉ U := fun hU => hrU (by
    have e : r = r * v * v⁻¹ := by group
    rw [e]
    exact mul_mem hU (inv_mem hv))
  rcases hx.cent h hrvR hcomm with e | e
  · exact hrvU (e ▸ U.one_mem)
  · exact hrvU (e ▸ h.z_mem)

theorem mul_sq (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) {r : G} (hrR : r ∈ R)
    (hrU : r ∉ U) : x * r * (x * r) = (r⁻¹ * (x * r * x⁻¹))⁻¹ := by
  have hrr : r * r = 1 := h.rot.mul_self r hrR hrU
  have hxx : x * x = 1 := hx.mul_self
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  set u := r⁻¹ * (x * r * x⁻¹) with hu
  have huU : u ∈ U := (hx.not_sq h hrR hrU).1
  have hru : r * u * r⁻¹ = u⁻¹ := h.rot.conj_eq r hrR hrU u huU
  calc x * r * (x * r) = r * (r⁻¹ * (x * r * x⁻¹)) * r := by rw [hxinv]; group
    _ = r * u * r⁻¹ := by rw [← hu, hrinv]
    _ = u⁻¹ := hru

theorem mul_sq_ne_one (h : Hyp Ω S K R U t z) (hx : Outer Ω S U x) {r : G} (hrR : r ∈ R)
    (hrU : r ∉ U) : x * r * (x * r) ≠ 1 := by
  rw [hx.mul_sq h hrR hrU]
  intro e
  apply (hx.not_sq h hrR hrU).2
  rw [inv_eq_one.mp e]
  exact IsSq.one

end Outer

theorem false_of_sq_mem (h : Hyp Ω S K R U t z) {y : G} (hy : Outer Ω S U y)
    (hsq : t * y * (t * y) ∈ R) (hty : t * y ∉ R) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := h.outer_t
  have htt : t * t = 1 := ht.mul_self
  have hyy : y * y = 1 := hy.mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  set u₁ := t * (y * t * y⁻¹) with hu₁
  have hu₁R : u₁ ∈ R := by
    have e : u₁ = t * y * (t * y) := by rw [hu₁, hyinv]; group
    rw [e]
    exact hsq
  have hu₁U : u₁ ∈ U := by
    by_contra hu₁U
    apply ht.mul_sq_ne_one h hu₁R hu₁U
    have e : t * u₁ = y * t * y⁻¹ := by rw [hu₁, ← mul_assoc, htt, one_mul]
    calc t * u₁ * (t * u₁) = y * (t * t) * y⁻¹ := by rw [e]; group
      _ = 1 := by rw [htt]; group
  have hyt : y * t * y⁻¹ = t * u₁ := by rw [hu₁, ← mul_assoc, htt, one_mul]
  obtain ⟨r, hrR, hrU⟩ := h.rot.exists_not_mem
  obtain ⟨hu₂U, hu₂⟩ := hy.not_sq h hrR hrU
  set u₂ := r⁻¹ * (y * r * y⁻¹) with hu₂def
  have hyr : y * r * y⁻¹ = r * u₂ := by rw [hu₂def]; group
  have hyU : ∀ u ∈ U, y * u * y⁻¹ = u⁻¹ := hy.inv h
  have htU : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ := ht.inv h
  by_cases hsq₁ : IsSq U u₁
  ·
    obtain ⟨v, hv, hvu⟩ := hsq₁
    set a := t * v with ha
    have haS : a ∈ S := mul_mem h.t_mem (h.le (h.rot.le hv))
    have hya : y * a = a * y := by
      have e1 : y * a * y⁻¹ = a := by
        calc y * a * y⁻¹ = (y * t * y⁻¹) * (y * v * y⁻¹) := by rw [ha]; group
          _ = t * (v * v) * v⁻¹ := by rw [hyt, hyU v hv, hvu]
          _ = a := by rw [ha]; group
      calc y * a = y * a * y⁻¹ * y := by group
        _ = a * y := by rw [e1]
    have haU : a ∉ U := fun haU => h.t_not_mem (by
      have e : t = a * v⁻¹ := by rw [ha]; group
      rw [e]
      exact mul_mem haU (inv_mem hv))
    have hzv : z * v ∈ U := mul_mem h.z_mem hv
    have hzaS : z * a ∈ S := mul_mem (h.le (h.rot.le h.z_mem)) haS
    have hza' : z * a = t * (z * v) := by
      have hzt : z * t = t * z := (h.z_central t h.t_mem).symm
      calc z * a = z * t * v := by rw [ha]; group
        _ = t * z * v := by rw [hzt]
        _ = t * (z * v) := by group
    have haZ : IsZInv Ω a := ht.mul_zinv h hv
    have hzaZ : IsZInv Ω (z * a) := hza' ▸ ht.mul_zinv h hzv
    have hzZ : IsZInv Ω z := ⟨K, h.mem, R, U, h.sylowR, h.rot, h.z_mem, h.z_ne, h.z_mul⟩
    have haa : a * a = 1 := (⟨haZ, haS, haU⟩ : Outer Ω S U a).mul_self
    have hza : z * a = a * z := (h.z_central a haS).symm
    have hzy : z * y = y * z := (h.z_central y hy.mem).symm
    obtain ⟨M, hM, T, V, hT, hV, hyV, hy1, -⟩ := hy.zinv
    have hyM : y ∈ M := hT.le (hV.le hyV)
    have hKM : K ≠ M := fun e => hy.not_mem_K h (e ▸ hyM)
    obtain ⟨y', hy'V, -, -, hy'uniq, hy'c⟩ := hV.exists_involution
    have hyy' : y = y' := (hy'uniq y hyV hyy).resolve_left hy1
    rw [← hyy'] at hy'c
    have hMt : TightlyEmbedded M := Assumption41.tightlyEmbedded h.asm hM
    have hCM : centralizer ({y} : Set G) ≤ normalizer (M : Set G) :=
      Asc76.Sec4.centralizer_le_normalizer hMt hyM hy1 hyy
    have hcomm_mem : ∀ c : G, c * y = y * c → c ∈ centralizer ({y} : Set G) := fun c hc => by
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hc.symm
    set A := fourGroup z a h.z_mul haa hza with hAdef
    have hz1 : z ≠ 1 := h.z_ne
    have ha1 : a ≠ 1 := fun e => haU (e ▸ U.one_mem)
    have hza1 : z ≠ a := fun e => haU (e ▸ h.z_mem)
    have hA4 : Nat.card A = 4 := card_fourGroup h.z_mul haa hza hz1 ha1 hza1
    have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 2) (by rw [hA4]; norm_num)
    have hAy : ∀ c ∈ A, c * y = y * c := by
      intro c hc
      rcases mem_fourGroup.mp hc with rfl | rfl | rfl | rfl
      · group
      · exact hzy
      · exact hya.symm
      · calc z * a * y = z * (a * y) := by group
          _ = z * (y * a) := by rw [← hya]
          _ = y * (z * a) := by rw [← mul_assoc, hzy, mul_assoc]
    have hAM : A ≤ normalizer (M : Set G) := fun c hc => hCM (hcomm_mem c (hAy c hc))
    have hAy' : A ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun c hc =>
      mem_normalizer_of_commute' fun w hw => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact ((Commute.zpow_left (hAy c hc).symm k).eq)
    have hTy : T ≤ normalizer ((zpowers y : Subgroup G) : Set G) := fun c hc =>
      mem_normalizer_of_commute' fun w hw => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact ((Commute.zpow_left (hy'c c hc).symm k).eq)
    obtain ⟨o, ho, hAT⟩ := exists_oddCore_normalizes hT (h.twoNil M hM T hT) hTy hA2 hAM hAy'
    have hoM : o ∈ M := oddCoreIn_le M (mem_inf.mp ho).1
    set T' := AschbacherTightEmbedding.rightConjugate T o⁻¹ with hT'def
    set V' := AschbacherTightEmbedding.rightConjugate V o⁻¹ with hV'def
    have hMo : AschbacherTightEmbedding.rightConjugate M o⁻¹ = M :=
      (rightConjugate_eq_self_iff M o⁻¹).mpr (le_normalizer (inv_mem hoM))
    have hT' : IsSylowOf 2 T' M := by
      have h1 := isSylowOf_rightConjugate hT o⁻¹
      rwa [hMo] at h1
    have hV' : IsDihedralRot V' T' := hV.rightConjugate o⁻¹
    have hyV' : y ∈ V' := by
      rw [hV'def, mem_rightConjugate_iff, inv_inv]
      have h1 : o⁻¹ * y * o⁻¹⁻¹ ∈ zpowers y :=
        (mem_normalizer_iff.mp (inv_mem (mem_inf.mp ho).2) y).mp (mem_zpowers y)
      rw [inv_inv] at h1
      rcases eq_of_mem_zpowers hyy h1 with e | e
      · exfalso
        apply hy1
        calc y = o * (o⁻¹ * y * o) * o⁻¹ := by group
          _ = 1 := by rw [e]; group
      · rw [e]
        exact hyV
    have hinv : ∀ e : G, e ∈ A → IsZInv Ω e → e ≠ 1 → e ∈ S →
        ∀ w ∈ V', e * w * e⁻¹ = w⁻¹ := by
      intro e heA heZ he1 heS
      obtain ⟨M', hM', T₁, V₁, hT₁, hV₁, heV₁, -, hee⟩ := heZ
      have heM' : e ∈ M' := hT₁.le (hV₁.le heV₁)
      have heM : e ∉ M := by
        intro heM
        have hey : e ≠ y := by
          intro e'
          rcases mem_fourGroup.mp heA with rfl | rfl | rfl | rfl
          · exact he1 rfl
          · exact hy.not_mem (e' ▸ h.z_mem)
          · apply hty
            rw [← e', ha, ← mul_assoc, htt, one_mul]
            exact h.rot.le hv
          · apply hty
            rw [← e', hza', ← mul_assoc, htt, one_mul]
            exact h.rot.le hzv
        have hey' : e * y = y * e := hAy e heA
        set Q := fourGroup e y hee hyy hey' with hQdef
        have hQ4 : Nat.card Q = 4 := card_fourGroup hee hyy hey' he1 hy1 hey
        have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 2) (by rw [hQ4]; norm_num)
        have hQM : Q ≤ M := by
          intro c hc
          rcases mem_fourGroup.mp hc with rfl | rfl | rfl | rfl
          · exact M.one_mem
          · exact heM
          · exact hyM
          · exact mul_mem heM hyM
        have hQK : Q ≤ normalizer (K : Set G) := by
          intro c hc
          apply h.le_normalizer_K
          rcases mem_fourGroup.mp hc with rfl | rfl | rfl | rfl
          · exact S.one_mem
          · exact heS
          · exact hy.mem
          · exact mul_mem heS hy.mem
        have h2 := h.card_le_two h.mem hM hKM hQ2 hQM hQK
        omega
      have hMM' : M ≠ M' := fun e' => heM (e' ▸ heM')
      exact conj_eq_inv_of_not_dStarAdj h.lemma22 h.asm hM' hM (h.not_dStarAdj hM hM' hMM')
        heM' he1 hee (hAM heA) hT' hV' (hAT heA)
    obtain ⟨w, hw, hwo⟩ := hV'.exists_gen
    have hwV : w ∈ V' := hw ▸ mem_zpowers w
    have h1 := hinv z (mem_fourGroup.mpr (Or.inr (Or.inl rfl))) hzZ hz1
      (h.le (h.rot.le h.z_mem)) w hwV
    have h2 := hinv a (mem_fourGroup.mpr (Or.inr (Or.inr (Or.inl rfl)))) haZ ha1 haS w hwV
    have h3 := hinv (z * a) (mem_fourGroup.mpr (Or.inr (Or.inr (Or.inr rfl)))) hzaZ
      (fun e => hza1 (by rw [eq_inv_of_mul_eq_one_left e, inv_eq_of_mul_eq_one_right haa]))
      hzaS w hwV
    apply hV'.gen_mul_self_ne_one hwo
    have e1 : z * a * w * (z * a)⁻¹ = w := by
      calc z * a * w * (z * a)⁻¹ = z * (a * w * a⁻¹) * z⁻¹ := by group
        _ = (z * w * z⁻¹)⁻¹ := by rw [h2]; group
        _ = w := by rw [h1, inv_inv]
    rw [h3] at e1
    calc w * w = w⁻¹ * w := by rw [e1]
      _ = 1 := inv_mul_cancel w
  ·
    obtain ⟨hu₀U, hu₀⟩ := ht.not_sq h hrR hrU
    set u₀ := r⁻¹ * (t * r * t⁻¹) with hu₀def
    set c := t * r with hc
    have hc2 : c * c = u₀⁻¹ := ht.mul_sq h hrR hrU
    have hc2U : c * c ∈ U := hc2 ▸ inv_mem hu₀U
    have hcU : ∀ u ∈ U, c * u = u * c := by
      intro u hu
      have hr' : r * u * r⁻¹ = u⁻¹ := h.rot.conj_eq r hrR hrU u hu
      have ht' : t * u⁻¹ * t⁻¹ = u := by rw [htU u⁻¹ (inv_mem hu), inv_inv]
      calc c * u = t * (r * u * r⁻¹) * r := by rw [hc]; group
        _ = t * u⁻¹ * t⁻¹ * (t * r) := by rw [hr']; group
        _ = u * c := by rw [ht', hc]
    have hyc : y * c * y⁻¹ = c * (u₁⁻¹ * u₂) := by
      have hru₁ : r * u₁ * r⁻¹ = u₁⁻¹ := h.rot.conj_eq r hrR hrU u₁ hu₁U
      have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right (h.rot.mul_self r hrR hrU)
      have hru₁' : r⁻¹ * u₁ * r = u₁⁻¹ := by
        rw [hrinv] at hru₁ ⊢
        exact hru₁
      calc y * c * y⁻¹ = (y * t * y⁻¹) * (y * r * y⁻¹) := by rw [hc]; group
        _ = t * u₁ * (r * u₂) := by rw [hyt, hyr]
        _ = t * r * (r⁻¹ * u₁ * r) * u₂ := by group
        _ = c * (u₁⁻¹ * u₂) := by rw [hru₁', hc]; group
    have hsqy : IsSq U (u₁⁻¹ * u₂) :=
      IsSq.mul_of_not h.rot (inv_mem hu₁U) hu₂U (IsSq.not_inv hsq₁) hu₂
    obtain ⟨w, hw, hwy⟩ := hsqy
    have hyc2 : y * (c * c) * y⁻¹ = (c * c)⁻¹ := hyU _ hc2U
    have hyc2' : y * (c * c) * y⁻¹ = c * c * (w * w * (w * w)) := by
      have hcw : c * (w * w) = w * w * c := hcU _ (mul_mem hw hw)
      calc y * (c * c) * y⁻¹ = (y * c * y⁻¹) * (y * c * y⁻¹) := by group
        _ = c * (w * w) * (c * (w * w)) := by rw [hyc, hwy]
        _ = c * (w * w * c) * (w * w) := by group
        _ = c * c * (w * w * (w * w)) := by rw [← hcw]; group
    have hw4 : w * w * (w * w) = u₀ * u₀ := by
      have e1 : c * c * (w * w * (w * w)) = (c * c)⁻¹ := by rw [← hyc2', hyc2]
      have e2 : w * w * (w * w) = (c * c)⁻¹ * (c * c)⁻¹ := by
        calc w * w * (w * w) = (c * c)⁻¹ * (c * c * (w * w * (w * w))) := by group
          _ = (c * c)⁻¹ * (c * c)⁻¹ := by rw [e1]
      rw [e2, hc2, inv_inv]
    have hwu : w * w * u₀⁻¹ * (w * w * u₀⁻¹) = 1 := by
      have hc1 : u₀⁻¹ * (w * w) = w * w * u₀⁻¹ :=
        h.rot.commute_of_mem (inv_mem hu₀U) (mul_mem hw hw)
      calc w * w * u₀⁻¹ * (w * w * u₀⁻¹) = w * w * (u₀⁻¹ * (w * w)) * u₀⁻¹ := by group
        _ = w * w * (w * w) * (u₀⁻¹ * u₀⁻¹) := by rw [hc1]; group
        _ = 1 := by rw [hw4]; group
    apply hu₀
    rcases h.z_unique _ (mul_mem (mul_mem hw hw) (inv_mem hu₀U)) hwu with e | e
    · refine ⟨w, hw, ?_⟩
      calc w * w = w * w * u₀⁻¹ * u₀ := by group
        _ = u₀ := by rw [e, one_mul]
    · have e' : u₀ = (w * w) * z := by
        have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_mul
        calc u₀ = (w * w * u₀⁻¹)⁻¹ * (w * w) := by group
          _ = w * w * z := by
            rw [e, hzinv]
            exact h.rot.commute_of_mem h.z_mem (mul_mem hw hw)
      rw [e']
      exact IsSq.mul h.rot ⟨w, hw, rfl⟩ h.isSq_z

theorem zinv_mem (h : Hyp Ω S K R U t z) {y : G} (hyZ : IsZInv Ω y) (hyS : y ∈ S) :
    y ∈ U ∨ y * t ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hyU, hytU⟩ := hcon
  have hy : Outer Ω S U y := ⟨hyZ, hyS, hyU⟩
  have ht := h.outer_t
  have htt : t * t = 1 := ht.mul_self
  have hyy : y * y = 1 := hy.mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  set c := t * y with hc
  have hcS : c ∈ S := mul_mem h.t_mem hyS
  have hcR : c ∉ R := by
    intro hcR
    apply hytU
    have hcU : c ∈ U := h.rot.mem_of_commute hcR fun u hu => by
      have h1 : y * u * y⁻¹ = u⁻¹ := hy.inv h u hu
      have h2 : t * u⁻¹ * t⁻¹ = u := by rw [ht.inv h u⁻¹ (inv_mem hu), inv_inv]
      calc c * u = t * (y * u * y⁻¹) * y := by rw [hc]; group
        _ = t * u⁻¹ * t⁻¹ * (t * y) := by rw [h1]; group
        _ = u * c := by rw [h2, hc]
    have e : y * t = c⁻¹ := by rw [hc, mul_inv_rev, htinv, hyinv]
    rw [e]
    exact inv_mem hcU
  have htc : ∀ m : ℕ, t * c ^ m * t⁻¹ = (c ^ m)⁻¹ := by
    intro m
    have h1 : t * c * t⁻¹ = c⁻¹ := by
      rw [hc, mul_inv_rev, htinv, hyinv, ← mul_assoc, htt, one_mul]
    rw [← conj_pow, h1, inv_pow]
  obtain ⟨n, hn⟩ := h.sylow.isPGroup ⟨c, hcS⟩
  have hn' : c ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hex : ∃ k : ℕ, c ^ (2 ^ k) ∈ R := ⟨n, by rw [hn']; exact R.one_mem⟩
  have hk₀ := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, c ^ (2 ^ j) ∉ R := fun j hj => Nat.find_min hex hj
  rcases hk : Nat.find hex with _ | _ | i
  · rw [hk, pow_zero, pow_one] at hk₀
    exact hcR hk₀
  · rw [hk, pow_one, pow_two] at hk₀
    exact h.false_of_sq_mem hy hk₀ hcR
  · set g := c ^ (2 ^ i) with hg
    have hgS : g ∈ S := pow_mem hcS _
    have hy' : Outer Ω S U (g⁻¹ * t * g) := by
      refine ⟨IsZInv.conj h.asm h.zinv g, mul_mem (mul_mem (inv_mem hgS) h.t_mem) hgS, ?_⟩
      intro hU
      apply h.t_not_mem
      have h1 := (mem_normalizer_iff.mp (h.le_normalizer_U hgS) _).mp hU
      have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
      rwa [e] at h1
    have hty' : t * (g⁻¹ * t * g) = c ^ (2 ^ (i + 1)) := by
      have h1 : t * g⁻¹ * t⁻¹ = g := by
        rw [hg]
        have h2 := htc (2 ^ i)
        calc t * (c ^ 2 ^ i)⁻¹ * t⁻¹ = (t * c ^ 2 ^ i * t⁻¹)⁻¹ := by group
          _ = c ^ 2 ^ i := by rw [h2, inv_inv]
      calc t * (g⁻¹ * t * g) = (t * g⁻¹ * t⁻¹) * (t * t) * g := by group
        _ = c ^ (2 ^ (i + 1)) := by rw [h1, htt, mul_one, hg, ← pow_add, pow_succ, mul_two]
    refine h.false_of_sq_mem hy' ?_ ?_
    · rw [hty', ← pow_add, ← two_mul, ← pow_succ']
      rw [hk] at hk₀
      exact hk₀
    · rw [hty']
      exact hmin (i + 1) (by rw [hk]; omega)

theorem t_mem_normalizer (h : Hyp Ω S K R U t z) : t ∈ normalizer (U : Set G) :=
  h.le_normalizer_U h.t_mem

omit [Finite G] in
theorem t_mul (h : Hyp Ω S K R U t z) : t * t = 1 :=
  h.outer_t.mul_self

@[expose] noncomputable def rPrime (h : Hyp Ω S K R U t z) : Subgroup G :=
  Hall32.dihedral U t h.t_mem_normalizer h.t_mul

theorem mem_rPrime (h : Hyp Ω S K R U t z) {x : G} : x ∈ h.rPrime ↔ x ∈ U ∨ x * t ∈ U :=
  Iff.rfl

theorem rPrime_le (h : Hyp Ω S K R U t z) : h.rPrime ≤ S := by
  intro x hx
  rcases h.mem_rPrime.mp hx with hxU | hxt
  · exact h.le (h.rot.le hxU)
  · have e : x = x * t * t := by rw [mul_assoc, h.t_mul, mul_one]
    rw [e]
    exact mul_mem (h.le (h.rot.le hxt)) h.t_mem

theorem stronglyClosed (h : Hyp Ω S K R U t z) :
    CFSG.Open.fusionStronglyClosed (h.rPrime : Set G) S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha g hg
  have hzZ : IsZInv Ω z := ⟨K, h.mem, R, U, h.sylowR, h.rot, h.z_mem, h.z_ne, h.z_mul⟩
  rcases h.mem_rPrime.mp ha with haU | hat
  · by_cases haa : a * a = 1
    · rcases h.z_unique a haU haa with rfl | rfl
      · rw [show g⁻¹ * 1 * g = 1 by group]
        exact one_mem _
      · exact h.mem_rPrime.mpr (h.zinv_mem (IsZInv.conj h.asm hzZ g) hg)
    ·
      set b := g⁻¹ * a * g with hb
      have hbb : b * b ≠ 1 := fun e => haa (by
        calc a * a = g * (b * b) * g⁻¹ := by rw [hb]; group
          _ = 1 := by rw [e]; group)
      have hb1 : b ≠ 1 := fun e => hbb (by rw [e, one_mul])
      have hbK' : b ∈ AschbacherTightEmbedding.rightConjugate K g := by
        rw [mem_rightConjugate_iff, hb]
        have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
        rw [e]
        exact h.sylowR.le (h.rot.le haU)
      have hKg : AschbacherTightEmbedding.rightConjugate K g = K := by
        by_contra hne
        have hQ2 : IsPGroup 2 (zpowers b) := h.sylow.isPGroup.to_le ((zpowers_le).mpr hg)
        have h2 := h.card_le_two h.mem (h.asm.conj_mem K h.mem g) (Ne.symm hne) hQ2
          ((zpowers_le).mpr hbK') ((zpowers_le).mpr (h.le_normalizer_K hg))
        have hbne : b ≠ b * b := fun e => hb1 (by
          have e' : b * 1 = b * b := by rw [mul_one]; exact e
          exact (mul_left_cancel e').symm)
        have h3 := three_le_card (one_mem (zpowers b)) (mem_zpowers b)
          (mul_mem (mem_zpowers b) (mem_zpowers b)) (Ne.symm hb1) (Ne.symm hbb) hbne
        omega
      rw [hKg] at hbK'
      exact h.mem_rPrime.mpr (Or.inl (h.rot.mem_of_mul_self_ne_one (h.mem_R hg hbK') hbb))
  ·
    have hta : t * a ∈ U := by
      have e : t * a = t * (a * t) * t⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp h.t_mem_normalizer _).mp hat
    have haZ : IsZInv Ω a := by
      have e : a = t * (t * a) := by rw [← mul_assoc, h.t_mul, one_mul]
      rw [e]
      exact h.outer_t.mul_zinv h hta
    exact h.mem_rPrime.mpr (h.zinv_mem (IsZInv.conj h.asm haZ g) hg)

end Hyp

end CFSG.ComponentClassification.Asc76X.HallDihedral
