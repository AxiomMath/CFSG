module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsS
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsTau
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveInner

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
open CFSG.GH74.GLS.Bg.Thompson

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

theorem two_mul_card_le_of_not_mem {H K : Subgroup G} (hHK : H ≤ K) {a : G} (haK : a ∈ K)
    (haH : a ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := card_dvd_of_le hHK
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with hm' | hm'
    · interval_cases m
      · omega
      · exfalso
        rw [mul_one] at hm
        exact haH (by rw [eq_of_le_of_card_ge hHK hm.le]; exact haK)
    · exact hm'
  calc 2 * Nat.card H ≤ m * Nat.card H := Nat.mul_le_mul_right _ hm2
    _ = Nat.card K := by rw [hm, mul_comm]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {a : G} {n : ℕ} (ha : a ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers a) := by
  have h1 : orderOf a ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one ha
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem mul_self_eq_one_of_isSylowOf {H E : Subgroup G} (hE : IsSylowOf 2 E H)
    (hE2 : ∀ e ∈ E, e * e = 1) {a : G} (ha : a ∈ H) (ha2 : IsPGroup 2 (zpowers a)) :
    a * a = 1 := by
  obtain ⟨Q, hQ, haQ⟩ := exists_isSylowOf_le (zpowers_le.mpr ha) ha2
  obtain ⟨c, -, hc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hE hQ
  have h1 : a ∈ Lemma34.conj E c := hc ▸ haQ (mem_zpowers a)
  rw [Lemma34.mem_conj_iff] at h1
  have h2 := hE2 _ h1
  calc a * a = c * ((c⁻¹ * a * c) * (c⁻¹ * a * c)) * c⁻¹ := by group
    _ = 1 := by rw [h2]; group

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem exists_elemAbelian_of_le_normalizer {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer (A : Set G)) (hQ32 : 32 ≤ Nat.card Q) :
    ∃ E ≤ Q, IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := h.equiv
  let φ : ↥Q →* ℤˣ := Perm.sign.comp ((autPerm eA).comp (Subgroup.inclusion hQN))
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup G, φ.ker.map Q.subtype = E₀ := ⟨_, rfl⟩
  have hE₀Q : E₀ ≤ Q := hE₀ ▸ map_subtype_le _
  have hE₀card : 16 ≤ Nat.card E₀ := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ 2 := by
      calc Nat.card φ.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
        _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    have h3 : Nat.card E₀ = Nat.card φ.ker := by
      rw [← hE₀, card_map_of_injective Q.subtype_injective]
    rw [h3]
    nlinarith
  have hsq : ∀ q ∈ E₀, q * q = 1 := by
    intro q hq
    rw [← hE₀] at hq
    obtain ⟨q', hq', rfl⟩ := mem_map.mp hq
    have hAK : (q' : G) ∈ A ⊔ centralizer (A : Set G) :=
      (mem_sup_iff_sign eA ⟨q', hQN q'.2⟩).mpr (MonoidHom.mem_ker.mp hq')
    obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup hAK
    obtain ⟨n, hn⟩ := hQ q'
    have hn' : (q' : G) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hcomm : Commute a k := mem_centralizer_iff.mp hk a ha
    have hpow : a ^ 2 ^ n * k ^ 2 ^ n = 1 := by rw [← hcomm.mul_pow, hak, hn']
    have ha1 : a ^ 2 ^ n = 1 := by
      have hmem : a ^ 2 ^ n ∈ A ⊓ centralizer (A : Set G) := by
        refine mem_inf.mpr ⟨pow_mem ha _, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hpow]
        exact inv_mem (pow_mem hk _)
      rw [inf_centralizer_eq_bot eA] at hmem
      exact mem_bot.mp hmem
    have hk1 : k ^ 2 ^ n = 1 := by
      rw [ha1, one_mul] at hpow
      exact hpow
    have ha2 : a * a = 1 := mul_self_eq_one_of_isSylowOf h.loc.sylowV₀
      (fun e he => h.mul_self (h.V₀_le he)) ha (isPGroup_zpowers_of_pow_eq_one ha1)
    have hk2 : k * k = 1 := mul_self_eq_one_of_isSylowOf h.sylowR
      (fun e he => h.mul_self (mem_sup_left he)) hk (isPGroup_zpowers_of_pow_eq_one hk1)
    show (q' : G) * q' = 1
    rw [← hak]
    calc a * k * (a * k) = a * (k * a) * k := by group
      _ = a * (a * k) * k := by rw [← hcomm.eq]
      _ = (a * a) * (k * k) := by group
      _ = 1 := by rw [ha2, hk2, one_mul]
  have hcomm₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have habi : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := habi.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hai, hbi]
  have hE₀e : IsElemAbelian 2 E₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm₀ a a.2 b b.2)⟩⟩, fun q hq => by rw [sq]; exact hsq q hq⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hQ.to_le hE₀Q)
  have hm4 : 4 ≤ m := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hm] at h1
    omega
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E₀) 2 (n := 4)
    (by rw [hm]; exact pow_dvd_pow 2 hm4)
  refine ⟨F.map E₀.subtype, (map_subtype_le F).trans hE₀Q,
    isElemAbelian_of_le hE₀e (map_subtype_le F), ?_⟩
  rw [card_map_of_injective E₀.subtype_injective, hF]
  norm_num

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V')
include hIIa hV'

variable (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G) (hP64 : Nat.card P = 64)
  (S : Sylow 2 G) (hS₁S : P ⊔ zpowers x ≤ S)
include hGold hGs hP64 hS₁S

theorem outer_card_centralizer :
    32 ≤ Nat.card ((S : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  obtain ⟨hSN₁, -, -, -, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have hxx : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have h4 : 4 ≤ Nat.card ((R ⊔ T) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have h1 := card_le_sq_card_inf_centralizer h.loc.elem hx.normV
      (by rw [hx.sq]; exact one_mem _)
    rw [h.loc.card] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card ((R ⊔ T) ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 9 :=
      calc _ ≤ 3 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 9 := by norm_num
    omega
  obtain ⟨v, hvV', hvV₀, hxv⟩ := h.outer_exists_mem_V' hx hV'
  have hvV : v ∉ R ⊔ T := fun hv => hvV₀ (hV'.inf ▸ mem_inf.mpr ⟨hv, hvV'⟩)
  have h8 := two_mul_card_le_of_not_mem (inf_le_inf_right (centralizer ({x} : Set G)) hVP)
    (mem_inf.mpr ⟨hV'.le hvV', mem_centralizer_singleton_iff.mpr hxv.symm⟩)
    (fun h' => hvV (mem_inf.mp h').1)
  have h16 := two_mul_card_le_of_not_mem
    (inf_le_inf_right (centralizer ({x} : Set G)) (le_sup_left : P ≤ P ⊔ zpowers x))
    (mem_inf.mpr ⟨mem_sup_right (mem_zpowers x), hxx⟩) (fun h' => hx.not_mem (mem_inf.mp h').1)
  obtain ⟨s₀, hs₀, hs₀S₁⟩ :=
    IsConcreteLE.exists_of_lt (h.outer_lt_sylow hP hPC hx hV' hGold hGs hP64 S hS₁S)
  have hu : s₀⁻¹ * x * s₀ ∈ P ⊔ zpowers x := by
    have := (mem_normalizer_iff.mp (hSN₁ (inv_mem hs₀)) x).mp (mem_sup_right (mem_zpowers x))
    rwa [inv_inv] at this
  have huP : s₀⁻¹ * x * s₀ ∉ P := by
    intro h'
    have h1 := (mem_normalizer_iff.mp
      (h.outer_le_normalizer_P hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S hs₀) _).mp h'
    have e : s₀ * (s₀⁻¹ * x * s₀) * s₀⁻¹ = x := by group
    rw [e] at h1
    exact hx.not_mem h1
  have hxu : x * (s₀⁻¹ * x * s₀) ∈ P := ((outer_mem_sup_iff hx).mp hu).resolve_left huP
  have hu2 : s₀⁻¹ * x * s₀ * (s₀⁻¹ * x * s₀) = 1 := by
    calc s₀⁻¹ * x * s₀ * (s₀⁻¹ * x * s₀) = s₀⁻¹ * (x * x) * s₀ := by group
      _ = 1 := by rw [hx.sq]; group
  obtain ⟨q, hqP, hq⟩ := h.outer_exists_conj_eq hP hPC hx hP64 hxu hu2
  have htx : q * s₀⁻¹ ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : x = s₀ * (q⁻¹ * x * q) * s₀⁻¹ := by
      rw [hq]
      group
    calc q * s₀⁻¹ * x = q * s₀⁻¹ * (s₀ * (q⁻¹ * x * q) * s₀⁻¹) := by rw [← e]
      _ = x * (q * s₀⁻¹) := by group
  have htS : q * s₀⁻¹ ∈ (S : Subgroup G) := mul_mem (hS₁S (mem_sup_left hqP)) (inv_mem hs₀)
  have htS₁ : q * s₀⁻¹ ∉ P ⊔ zpowers x := by
    intro h'
    apply hs₀S₁
    have h1 := mul_mem (inv_mem h') (mem_sup_left hqP : q ∈ P ⊔ zpowers x)
    have e : (q * s₀⁻¹)⁻¹ * q = s₀ := by group
    rwa [e] at h1
  have h32 := two_mul_card_le_of_not_mem
    (inf_le_inf_right (centralizer ({x} : Set G)) hS₁S) (mem_inf.mpr ⟨htS, htx⟩)
    (fun h' => htS₁ (mem_inf.mp h').1)
  omega

theorem outer_not_isRootInv : ¬ IsRootInv A x := by
  rintro ⟨c, hxc⟩
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hx1 : x ≠ 1 := fun h1 => hx.not_mem (h1 ▸ one_mem P)
  have hxK : x ∈ centralizer (rightConjugate A c : Set G) := by
    rw [centralizer_rightConjugate]
    exact hxc
  have hCN := centralizer_le_normalizer_conj h.hyp.standard c hxK hx1 hx.sq
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, (S : Subgroup G) ⊓ centralizer ({x} : Set G) = Q :=
    ⟨_, rfl⟩
  have hQ' : rightConjugate Q c⁻¹ ≤ normalizer (A : Set G) := by
    intro a ha
    rw [mem_rightConjugate_iff, inv_inv] at ha
    have h1 := hCN (mem_inf.mp (hQ ▸ ha)).2
    rw [mem_normalizer_rightConjugate_iff] at h1
    have e : c * (c⁻¹ * a * c) * c⁻¹ = a := by group
    rwa [e] at h1
  have hQp : IsPGroup 2 (rightConjugate Q c⁻¹) :=
    (S.isPGroup'.to_le (hQ ▸ inf_le_left)).map (MulAut.conj c⁻¹⁻¹).toMonoidHom
  have hQ32 : 32 ≤ Nat.card (rightConjugate Q c⁻¹) := by
    rw [rightConjugate_card, ← hQ]
    exact h.outer_card_centralizer hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  obtain ⟨E, hEQ, hEe, hE16⟩ := h.exists_elemAbelian_of_le_normalizer hQp hQ' hQ32
  have hE'Q : rightConjugate E c ≤ Q := by
    intro b hb
    rw [mem_rightConjugate_iff] at hb
    have h1 := hEQ hb
    rw [mem_rightConjugate_iff] at h1
    have e : c⁻¹ * (c * b * c⁻¹) * c⁻¹⁻¹ = b := by group
    rwa [e] at h1
  obtain ⟨-, -, -, -, hES⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have hE'S : rightConjugate E c ≤ S := hE'Q.trans (hQ ▸ inf_le_left)
  have hE'x : ∀ w ∈ rightConjugate E c, w * x = x * w := fun w hw =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hQ ▸ hE'Q hw)).2
  apply h.outer_not_mem_centralizer_V₀ hx
  rw [mem_centralizer_iff]
  intro w hw
  rcases hES _ hE'S (isElemAbelian_rightConjugate hEe c) (by rw [rightConjugate_card, hE16]) with
    h1 | h1
  · exact hE'x w (by rw [h1]; exact h.V₀_le hw)
  · exact hE'x w (by rw [h1]; exact hV₀V' hw)

omit hGold hGs hP64 hS₁S in
theorem outer_exists_sq_eq_z : ∃ c ∈ P, x * c = c * x ∧ c * c = z := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  obtain ⟨v, hvV', hvV₀, hxv⟩ := h.outer_exists_mem_V' hx hV'
  have hr₁P : r₁ ∈ P := hVP (mem_sup_left hx.r_mem)
  have hvP : v ∈ P := hV'.le hvV'
  have hvV : v ∉ R ⊔ T := fun hv => hvV₀ (hV'.inf ▸ mem_inf.mpr ⟨hv, hvV'⟩)
  refine ⟨r₁ * v, mul_mem hr₁P hvP, ?_, ?_⟩
  · calc x * (r₁ * v) = x * r₁ * v := (mul_assoc _ _ _).symm
      _ = r₁ * x * v := by rw [hx.r_comm]
      _ = r₁ * (x * v) := mul_assoc _ _ _
      _ = r₁ * (v * x) := by rw [hxv]
      _ = r₁ * v * x := (mul_assoc _ _ _).symm
  · have hr₁2 : r₁ * r₁ = 1 := h.mul_self (mem_sup_left hx.r_mem)
    have hv2 : v * v = 1 := by
      rw [← sq]
      exact hV'.elem.2 v hvV'
    have hc : r₁ * v * r₁⁻¹ * v⁻¹ ∈ V₀ := h.P_comm_mem_V₀ hP hPC hIIa hr₁P hvP
    have e : r₁ * v * (r₁ * v) = r₁ * v * r₁⁻¹ * v⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hr₁2, inv_eq_of_mul_eq_one_right hv2]
      group
    rw [e]
    have hxr : x * r₁ * x⁻¹ = r₁ := by
      rw [hx.r_comm]
      group
    have hxv' : x * v * x⁻¹ = v := by
      rw [hxv]
      group
    have hcx : x * (r₁ * v * r₁⁻¹ * v⁻¹) = r₁ * v * r₁⁻¹ * v⁻¹ * x := by
      calc x * (r₁ * v * r₁⁻¹ * v⁻¹) =
          (x * r₁ * x⁻¹) * (x * v * x⁻¹) * (x * r₁ * x⁻¹)⁻¹ * (x * v * x⁻¹)⁻¹ * x := by group
        _ = r₁ * v * r₁⁻¹ * v⁻¹ * x := by rw [hxr, hxv']
    rcases hx.fix_V₀ _ hc hcx with h1 | h1
    · exfalso
      have hcomm : v * r₁ * v⁻¹ = r₁ := by
        calc v * r₁ * v⁻¹ = (r₁ * v * r₁⁻¹ * v⁻¹)⁻¹ * r₁ := by group
          _ = r₁ := by rw [h1, inv_one, one_mul]
      have hr₁V₀ := h.P_fixed hP hPC hvP hvV (mem_sup_left hx.r_mem) hcomm
      have h2 : r₁ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hx.r_mem, hr₁V₀⟩
      rw [h.inf_R_V₀] at h2
      exact hx.r_ne (mem_bot.mp h2)
    · exact h1

theorem outer_false : False := by
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  obtain ⟨-, -, -, hswap, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have hxS : x ∈ (S : Subgroup G) := hS₁S (mem_sup_right (mem_zpowers x))
  have hPS : P ≤ (S : Subgroup G) := le_sup_left.trans hS₁S
  have hxC := h.outer_not_mem_centralizer_V₀ hx
  have hxroot := h.outer_not_isRootInv hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have hCx := h.outer_card_centralizer hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have hzS : ∀ t ∈ (S : Subgroup G), t * z = z * t := fun t ht =>
    h.outer_comm_z hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S ht
  have hroot : ∀ {u : G}, u ∈ P → u * u = 1 → u ∉ V₀ → IsRootInv A u := by
    intro u huP hu2 hu0
    by_cases huV : u ∈ R ⊔ T
    · exact h.isRootInv_of_mem_V huV hu0
    · exact h.outer_isRootInv_of_mem_V' hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
        (hV'.inv u huP hu2 huV) hu0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkU, hkext, hkC⟩ := exists_extremal_conj hGs h.not_isPGroup_two S.isPGroup'
    S.not_dvd_index inf_le_left
    (h.outer_relIndex_centralizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S) hxS
    (fun h' => hxC (mem_inf.mp h').2) hx.sq
  have hy2 : k⁻¹ * x * k * (k⁻¹ * x * k) = 1 := by
    calc k⁻¹ * x * k * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
      _ = 1 := by rw [hx.sq]; group
  have hxy : IsConj x (k⁻¹ * x * k) := isConj_iff.mpr ⟨k⁻¹, by group⟩
  have hφcard :
      32 ≤ Nat.card ((S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G) : Subgroup G) := by
    have hle : rightConjugate ((S : Subgroup G) ⊓ centralizer ({x} : Set G)) k ≤
        (S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G) := by
      intro b hb
      rw [mem_rightConjugate_iff] at hb
      have h1 := hkC _ hb
      have e : k⁻¹ * (k * b * k⁻¹) * k = b := by group
      rwa [e] at h1
    calc 32 ≤ Nat.card ((S : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) := hCx
      _ = Nat.card (rightConjugate ((S : Subgroup G) ⊓ centralizer ({x} : Set G)) k) :=
        (rightConjugate_card _ _).symm
      _ ≤ _ := card_le_of_le hle
  have hyroot : ¬ IsRootInv A (k⁻¹ * x * k) := fun hr => hxroot (hr.of_isConj hxy.symm)
  obtain ⟨hyS, hyC⟩ := mem_inf.mp hkU
  have hyP : k⁻¹ * x * k ∈ P := by
    by_contra hyP
    have hyS₁ : k⁻¹ * x * k ∉ P ⊔ zpowers x := fun h' =>
      hyP (h.outer_mem_P_of_mem_centralizer_V₀ hP hx h' hyC)
    obtain ⟨hyV, hyV'⟩ := hswap _ hyS hyS₁
    have hCP := h.swap_inf_centralizer_le hP hPC hIIa hV' hyV hyV' hyC hy2
    have h4 := h.outer_relIndex_P hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
    have hle4 : P.relIndex ((S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G)) ≤ 4 := by
      have h1 := Subgroup.relIndex_le_of_le_right (H := P)
        (inf_le_left : (S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G) ≤ S) (by
          rw [h4]
          norm_num)
      exact h1.trans (le_of_eq h4)
    have hPy : Nat.card (P ⊓ ((S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G)) :
        Subgroup G) ≤ 4 := by
      have hle : P ⊓ ((S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G)) ≤ V₀ :=
        fun b hb => hCP (mem_inf.mpr ⟨(mem_inf.mp hb).1, (mem_inf.mp (mem_inf.mp hb).2).2⟩)
      exact (card_le_of_le hle).trans (le_of_eq h.card_V₀)
    have h1 := Subgroup.relIndex_mul_card P
      ((S : Subgroup G) ⊓ centralizer ({k⁻¹ * x * k} : Set G))
    have h2 := Nat.mul_le_mul hle4 hPy
    omega
  have hyV₀ : k⁻¹ * x * k ∈ V₀ := by
    by_contra hy0
    exact hyroot (hroot hyP hy2 hy0)
  have hy1 : k⁻¹ * x * k ≠ 1 := by
    intro h1
    apply hx.not_mem
    have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [e, h1, mul_one, mul_inv_cancel]
    exact one_mem P
  have hSy : (S : Subgroup G) ≤ centralizer ({k⁻¹ * x * k} : Set G) :=
    le_centralizer_of_isExtremalIn S.isPGroup' hzS
      (h.isConj_of_mem_V₀ hx.z_mem hx.z_ne hyV₀ hy1) hkext
  have hyz : k⁻¹ * x * k = z := by
    rcases hx.fix_V₀ _ hyV₀ (mem_centralizer_singleton_iff.mp (hSy hxS)) with h1 | h1
    · exact absurd h1 hy1
    · exact h1
  obtain ⟨c₀, hc₀P, hc₀x, hc₀z⟩ := h.outer_exists_sq_eq_z hP hPC hx hIIa hV'
  have hc₀C : c₀ ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    mem_inf.mpr ⟨hPS hc₀P, mem_centralizer_singleton_iff.mpr hc₀x.symm⟩
  obtain ⟨hc₀S, -⟩ := mem_inf.mp (hkC c₀ hc₀C)
  have hz'P : k⁻¹ * z * k ∈ P := by
    have h1 := h.outer_sq_mem hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S hc₀S
    have e : k⁻¹ * c₀ * k * (k⁻¹ * c₀ * k) = k⁻¹ * z * k := by
      rw [← hc₀z]
      group
    rwa [e] at h1
  have hz'2 : k⁻¹ * z * k * (k⁻¹ * z * k) = 1 := by
    calc k⁻¹ * z * k * (k⁻¹ * z * k) = k⁻¹ * (z * z) * k := by group
      _ = 1 := by rw [h.mul_self (h.V₀_le hx.z_mem)]; group
  have hz'1 : k⁻¹ * z * k ≠ 1 := by
    intro h1
    apply hx.z_ne
    calc z = k * (k⁻¹ * z * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hz'V₀ : k⁻¹ * z * k ∈ V₀ := by
    by_contra hz0
    exact h.not_isRootInv_of_isConj hx.z_mem hx.z_ne (isConj_iff.mpr ⟨k⁻¹, by group⟩)
      (hroot hz'P hz'2 hz0)
  have hz'z : k⁻¹ * z * k ≠ z := by
    intro h1
    have e : z = x := by
      calc z = k * (k⁻¹ * z * k) * k⁻¹ := by group
        _ = k * (k⁻¹ * x * k) * k⁻¹ := by rw [h1, hyz]
        _ = x := by group
    exact hx.not_mem (e ▸ hVP (h.V₀_le hx.z_mem))
  have hφU : ∀ c ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G),
      k⁻¹ * c * k ∈ centralizer (V₀ : Set G) := by
    intro c hc
    obtain ⟨hcS', -⟩ := mem_inf.mp (hkC c hc)
    have hcz := hzS c (mem_inf.mp hc).1
    refine h.outer_mem_centralizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S hz'V₀ hz'1 hz'z
      hcS' ?_
    calc k⁻¹ * c * k * (k⁻¹ * z * k) = k⁻¹ * (c * z) * k := by group
      _ = k⁻¹ * (z * c) * k := by rw [hcz]
      _ = k⁻¹ * z * k * (k⁻¹ * c * k) := by group
  have hr₁C : r₁ ∈ (S : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    mem_inf.mpr ⟨hPS (hVP (mem_sup_left hx.r_mem)),
      mem_centralizer_singleton_iff.mpr hx.r_comm.symm⟩
  obtain ⟨hdS, -⟩ := mem_inf.mp (hkC r₁ hr₁C)
  have hdC := hφU r₁ hr₁C
  have hd2 : k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = 1 := by
    calc k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = k⁻¹ * (r₁ * r₁) * k := by group
      _ = 1 := by rw [h.mul_self (mem_sup_left hx.r_mem)]; group
  have hd1 : k⁻¹ * r₁ * k ≠ 1 := by
    intro h1
    apply hx.r_ne
    calc r₁ = k * (k⁻¹ * r₁ * k) * k⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hdroot : IsRootInv A (k⁻¹ * r₁ * k) := (h.isRootInv_of_mem_R hx.r_mem).conj k
  have hdV₀ : k⁻¹ * r₁ * k ∉ V₀ := fun h0 =>
    h.not_isRootInv_of_isConj h0 hd1 (IsConj.refl _) hdroot
  have hzd : ¬ IsRootInv A (z * (k⁻¹ * r₁ * k)) := by
    intro hr
    apply hxroot
    obtain ⟨r, -, hr'⟩ := h.outer_exists_conj_mul_r hx
    have e : z * (k⁻¹ * r₁ * k) = k⁻¹ * (x * r₁) * k := by
      rw [← hyz]
      group
    rw [e] at hr
    refine hr.of_isConj ((isConj_iff.mpr ⟨k, by group⟩ :
      IsConj (k⁻¹ * (x * r₁) * k) (x * r₁)).trans (isConj_iff.mpr ⟨r, ?_⟩))
    rw [← hr']
    group
  apply hzd
  by_cases hdP : k⁻¹ * r₁ * k ∈ P
  · refine hroot (mul_mem (hVP (h.V₀_le hx.z_mem)) hdP) ?_ fun h0 => hdV₀ ?_
    · have hdz : k⁻¹ * r₁ * k * z = z * (k⁻¹ * r₁ * k) :=
        (mem_centralizer_iff.mp hdC z hx.z_mem).symm
      calc z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) =
          z * (k⁻¹ * r₁ * k * z) * (k⁻¹ * r₁ * k) := by group
        _ = z * (z * (k⁻¹ * r₁ * k)) * (k⁻¹ * r₁ * k) := by rw [hdz]
        _ = z * z * (k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k)) := by group
        _ = 1 := by rw [h.mul_self (h.V₀_le hx.z_mem), hd2, one_mul]
    · have h1 := mul_mem (inv_mem hx.z_mem) h0
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
  · have hdS₁ : k⁻¹ * r₁ * k ∉ P ⊔ zpowers x := fun h' =>
      hdP (h.outer_mem_P_of_mem_centralizer_V₀ hP hx h' hdC)
    obtain ⟨-, hdV'⟩ := hswap _ hdS hdS₁
    obtain ⟨q, -, hq⟩ := h.swap_exists_conj_eq_mul hP hPC hIIa hV' hdV' hdC hd2 hx.z_mem
    have hdz : k⁻¹ * r₁ * k * z = z * (k⁻¹ * r₁ * k) :=
      (mem_centralizer_iff.mp hdC z hx.z_mem).symm
    rw [← hdz]
    exact hdroot.of_isConj (isConj_iff.mpr ⟨q⁻¹, by rw [inv_inv]; exact hq⟩)

end PStructure

end Setting310

theorem asc310EpsOne_of (hGold : Asc76X.GoldschmidtTheoremA) : Asc310EpsOne := by
  intro G _ _ A R g T V₀ h _ hGs hIIa P hP hVP hPC hP64
  by_contra hε
  obtain ⟨V', hV'⟩ := h.exists_isVprime hP hPC hIIa hP64 hVP
  obtain ⟨x, z, r₁, hx⟩ := h.exists_outerInvol hP hPC hP64 hVP hε
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (h.outer_isSylowOf_sup hP hPC hx hP64).isPGroup.exists_le_sylow
  exact h.outer_false hP hPC hx hIIa hV' hGold hGs hP64 S hS

end CFSG.ComponentClassification.RankTwoAltFive
