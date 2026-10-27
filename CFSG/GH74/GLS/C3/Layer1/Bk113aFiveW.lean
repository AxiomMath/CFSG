module

public import CFSG.GH74.GLS.C3.Layer1.Bk113aGen
public import CFSG.GH74.GLS.C3.Layer1.BkP46W

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}

omit [Finite G] in
theorem C_le_normalizer_of_normal (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    centralizer ({x} : Set G) ≤ normalizer (K : Set G) :=
  fun c hc => mem_normalizer_of_two_sided (fun w hw => hKN c hc w hw) (fun w hw => by
    simpa using hKN c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) w hw)

omit [Finite G] in
theorem five_R_le_normalizer_W (hh : Hyp9A x K L M T Q)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    (T ⊓ K) ⊔ Q ≤ normalizer (pPrimeCoreOf 2 K : Set G) := by
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left (Setup91.Q_le_T hh)
  exact fun r hr => TwoThin.mem_normalizer_pPrimeCoreOf
    (C_le_normalizer_of_normal hKN (hh.sylowT.le (hRT hr)))

omit [Finite G] in
theorem five_K_normalizes_sup (hh : Hyp9A x K L M T Q)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hCD : CommDisj (T ⊓ K) Q) {k : G} (hk : k ∈ K)
    (hP : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K, ∃ w ∈ pPrimeCoreOf 2 K, k * p * k⁻¹ = p' * w) :
    ∀ z ∈ ((T ⊓ K) ⊔ Q) ⊔ pPrimeCoreOf 2 K, k * z * k⁻¹ ∈ ((T ⊓ K) ⊔ Q) ⊔ pPrimeCoreOf 2 K := by
  intro z hz
  have hRN := five_R_le_normalizer_W hh hKN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN] at hz
  obtain ⟨r, hr, w₀, hw₀, rfl⟩ := hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm hr
  obtain ⟨p', hp', w₁, hw₁, hpp'⟩ := hP p hp
  have hkq : k * q * k⁻¹ = ⁅k, q⁆ * q := by
    simp only [commutatorElement_def]
    group
  have hcomm : ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := (mem_CxK_of_mem_Q hh hq).2.2.2 k hk
  have hkw : k * w₀ * k⁻¹ ∈ pPrimeCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.1 (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk))
      w₀).1 hw₀
  have e : k * (p * q * w₀) * k⁻¹ = (k * p * k⁻¹) * (k * q * k⁻¹) * (k * w₀ * k⁻¹) := by group
  rw [e, hpp', hkq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left hp')) (Subgroup.mem_sup_right hw₁))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hq)))) (Subgroup.mem_sup_right hkw)

theorem five_w (hh : Hyp9A x K L M T Q)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (e5 : kBar K ≃* alternatingGroup (Fin 5)) (hCD : CommDisj (T ⊓ K) Q)
    (hR2 : IsPGroup 2 ↥((T ⊓ K) ⊔ Q)) :
    ∃ w ∈ K, (∃ e : ℕ, w ^ (3 ^ e) = 1) ∧
      w ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ∧
      (∀ q ∈ Q, w * q = q * w) ∧ (∀ p ∈ T ⊓ K, w * p * w⁻¹ = p → p = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := hh.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := hh.sylowT.le
  have hKC : K ≤ centralizer ({x} : Set G) := hh.K_le_centralizer
  obtain ⟨ψ, hker, hψK⟩ :=
    lemma113d_alt hKC hKN (n := 5) (by norm_num) (by norm_num) e5
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt5 hT2 (Setup91.inf_isSylowOf hh) e5
  have hWodd : Odd (Nat.card ↥(pPrimeCoreOf 2 K)) := TwoThin.card_pPrimeCoreOf_odd K
  have hRN := five_R_le_normalizer_W hh hKN
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left (Setup91.Q_le_T hh)
  have hψW : ∀ (k : G) (hk : k ∈ K), k ∈ pPrimeCoreOf 2 K → ψ ⟨k, hKC hk⟩ = 1 := by
    intro k hk hkW
    rw [hψK k hk]
    have : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Setup91.mem_pPrimeCoreOf_iff.1 hkW).2
    rw [this, map_one]
    rfl
  have hψ1 : ∀ (k : G) (hk : k ∈ K), ψ ⟨k, hKC hk⟩ = 1 → k ∈ pPrimeCoreOf 2 K := by
    intro k hk h1
    rw [hψK k hk] at h1
    have h2 : e5 (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) = 1 := Subtype.ext h1
    have h3 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 :=
      e5.injective (h2.trans (map_one e5).symm)
    exact Setup91.mem_pPrimeCoreOf_iff.2 ⟨hk, (QuotientGroup.eq_one_iff _).1 h3⟩
  have hψι : ∀ (p : G) (hp : p ∈ T ⊓ K), ψ ⟨p, hTC hp.1⟩ =
      ((ι ⟨p, hp⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := by
    intro p hp
    rw [hι ⟨p, hp⟩]
    exact hψK p hp.2
  have hconjψ : ∀ (u v : G) (hu : u ∈ centralizer ({x} : Set G)) (hv : v ∈ centralizer ({x} : Set G)),
      ψ ⟨u * v * u⁻¹, (centralizer ({x} : Set G)).mul_mem
        ((centralizer ({x} : Set G)).mul_mem hu hv) ((centralizer ({x} : Set G)).inv_mem hu)⟩ =
        ψ ⟨u, hu⟩ * ψ ⟨v, hv⟩ * (ψ ⟨u, hu⟩)⁻¹ := by
    intro u v hu hv
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨g, hg1, hg2⟩ := exists_normalizing_not_mem hιcard
  obtain ⟨hg3, hgfpf⟩ : g ^ 3 = 1 ∧ ∀ y ∈ ι.range, g * y * g⁻¹ = y → y = 1 :=
    (normalizer_X_cases hιcard g hg1).resolve_left hg2
  obtain ⟨a', ha'⟩ := e5.surjective g
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective a'
  have hk₀K : (k' : G) ∈ K := k'.2
  have hψk₀ : ψ ⟨(k' : G), hKC hk₀K⟩ = (g : Equiv.Perm (Fin 5)) := by
    rw [hψK (k' : G) hk₀K]
    have : (⟨(k' : G), hk₀K⟩ : ↥K) = k' := rfl
    rw [this, ha']
  have hP₀ : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K, ∃ w ∈ pPrimeCoreOf 2 K,
      (k' : G) * p * (k' : G)⁻¹ = p' * w := by
    intro p hp
    obtain ⟨p', hp'⟩ := hg1 (ι ⟨p, hp⟩) ⟨⟨p, hp⟩, rfl⟩
    refine ⟨(p' : G), p'.2, (p' : G)⁻¹ * ((k' : G) * p * (k' : G)⁻¹), ?_, by group⟩
    have hmemK : (p' : G)⁻¹ * ((k' : G) * p * (k' : G)⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem p'.2.2) (K.mul_mem (K.mul_mem hk₀K hp.2) (K.inv_mem hk₀K))
    refine hψ1 _ hmemK ?_
    have hp'C : (p' : G) ∈ centralizer ({x} : Set G) := hTC p'.2.1
    have hpC : p ∈ centralizer ({x} : Set G) := hTC hp.1
    have hk₀C : (k' : G) ∈ centralizer ({x} : Set G) := hKC hk₀K
    have e1 : (⟨(p' : G)⁻¹ * ((k' : G) * p * (k' : G)⁻¹), hKC hmemK⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨(p' : G), hp'C⟩ : ↥(centralizer ({x} : Set G)))⁻¹ *
          ⟨(k' : G) * p * (k' : G)⁻¹, (centralizer ({x} : Set G)).mul_mem
            ((centralizer ({x} : Set G)).mul_mem hk₀C hpC) ((centralizer ({x} : Set G)).inv_mem hk₀C)⟩ :=
      rfl
    rw [e1, map_mul, map_inv, hconjψ _ _ hk₀C hpC, hψk₀, hψι p hp, hψι (p' : G) p'.2]
    have h2 : ((ι p' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        (g : Equiv.Perm (Fin 5)) * ((ι ⟨p, hp⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) *
          (g : Equiv.Perm (Fin 5))⁻¹ := by
      rw [hp']
      rfl
    rw [h2]
    group
  have hk₀N : (k' : G) ∈ normalizer ((((T ⊓ K) ⊔ Q) ⊔ pPrimeCoreOf 2 K : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_le (five_K_normalizes_sup hh hKN hCD hk₀K hP₀)
  obtain ⟨w₀, hw₀, hnorm⟩ := frattini_odd hR2 hRN hWodd hk₀N
  have hw₀K : w₀ ∈ K := (Setup91.mem_pPrimeCoreOf_iff.1 hw₀).1
  have hwK : w₀ * (k' : G) ∈ K := K.mul_mem hw₀K hk₀K
  have hwC : w₀ * (k' : G) ∈ centralizer ({x} : Set G) := hKC hwK
  have hψw : ψ ⟨w₀ * (k' : G), hwC⟩ = (g : Equiv.Perm (Fin 5)) := by
    have e1 : (⟨w₀ * (k' : G), hwC⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨w₀, hKC hw₀K⟩ * ⟨(k' : G), hKC hk₀K⟩ := rfl
    rw [e1, map_mul, hψW w₀ hw₀K hw₀, hψk₀, one_mul]
  set w : G := w₀ * (k' : G) with hwdef
  have hwQ : ∀ q ∈ Q, w * q = q * w := by
    intro q hq
    have hqR : q ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right hq
    have hwq1 : w * q * w⁻¹ ∈ (T ⊓ K) ⊔ Q := (Subgroup.mem_normalizer_iff.1 hnorm q).1 hqR
    have hNxK : w ∈ NxK x K := ⟨hwC, Subgroup.le_normalizer hwK⟩
    have hwq2 : w * q * w⁻¹ ∈ CxK x K :=
      (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hNxK) q).1
        (mem_CxK_of_mem_Q hh hq)
    have hwq : w * q * w⁻¹ ∈ Q := by
      rw [hh.hQ]
      exact ⟨hRT hwq1, hwq2⟩
    have hcomm : ⁅w, q⁆ ∈ pPrimeCoreOf 2 K := (mem_CxK_of_mem_Q hh hq).2.2.2 _ hwK
    have hcommQ : ⁅w, q⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hwq (Q.inv_mem hq)
    have hbot := Setup91.inf_pPrimeCoreOf_eq_bot K hT2
    have h1 : ⁅w, q⁆ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hRT (Subgroup.mem_sup_right hcommQ), hcomm⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hw3 : w ^ 3 ∈ pPrimeCoreOf 2 K := by
    have hw3K : w ^ 3 ∈ K := K.pow_mem hwK 3
    refine hψ1 _ hw3K ?_
    have e1 : (⟨w ^ 3, hKC hw3K⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) ^ 3 := rfl
    rw [e1, map_pow, hψw]
    have := congrArg (fun z : alternatingGroup (Fin 5) => (z : Equiv.Perm (Fin 5))) hg3
    simpa using this
  have hodd : Odd (orderOf w) := by
    have h1 : orderOf (w ^ 3) ∣ Nat.card ↥(pPrimeCoreOf 2 K) := Subgroup.orderOf_dvd_natCard _ hw3
    have hodd3 : Odd (orderOf (w ^ 3)) := Odd.of_dvd_nat hWodd h1
    have h2 : orderOf w ∣ 3 * orderOf (w ^ 3) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact Odd.of_dvd_nat (Odd.mul (by decide) hodd3) h2
  have hord0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
  obtain ⟨a, b, hb3, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord0 3 (by norm_num)
  have hwb : (w ^ b) ^ (3 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hab]
    exact pow_orderOf_eq_one w
  obtain ⟨c, hc⟩ : ∃ c : ℕ, b * c % 3 = 1 := by
    have hcop : Nat.Coprime b 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb3 |>.symm
    obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
    exact ⟨c, hc⟩
  have hgbc : (g ^ b) ^ c = g := by
    have h1 : g ^ (b * c) = g ^ (b * c % 3) := by
      conv_lhs => rw [← Nat.div_add_mod (b * c) 3, pow_add, pow_mul, hg3, one_pow, one_mul]
    rw [← pow_mul, h1, hc, pow_one]
  refine ⟨w ^ b, K.pow_mem hwK b, ⟨a, hwb⟩, ?_, ?_, ?_⟩
  · exact Subgroup.pow_mem _ hnorm b
  · intro q hq
    exact ((Commute.pow_left (show Commute w q from hwQ q hq) b)).eq
  ·
    intro p hp hwp
    have hpC : p ∈ centralizer ({x} : Set G) := hTC hp.1
    have hwbC : w ^ b ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).pow_mem hwC b
    have h1 := hconjψ _ _ hwbC hpC
    have hmemC : (w ^ b) * p * (w ^ b)⁻¹ ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hwbC hpC)
        ((centralizer ({x} : Set G)).inv_mem hwbC)
    have h2 : ψ ⟨(w ^ b) * p * (w ^ b)⁻¹, hmemC⟩ = ψ ⟨p, hpC⟩ := by
      congr 1
      exact Subtype.ext hwp
    have hψwb : ψ ⟨w ^ b, hwbC⟩ = (g : Equiv.Perm (Fin 5)) ^ b := by
      have e1 : (⟨w ^ b, hwbC⟩ : ↥(centralizer ({x} : Set G))) =
          (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) ^ b := rfl
      rw [e1, map_pow, hψw]
    rw [h1, hψwb, hψι p hp] at h2
    have h3 : ∀ j : ℕ, (g ^ b) ^ j * ι ⟨p, hp⟩ * ((g ^ b) ^ j)⁻¹ = ι ⟨p, hp⟩ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h4 : g ^ b * ι ⟨p, hp⟩ * (g ^ b)⁻¹ = ι ⟨p, hp⟩ := by
          apply Subtype.ext
          simpa using h2
        calc (g ^ b) ^ (j + 1) * ι ⟨p, hp⟩ * ((g ^ b) ^ (j + 1))⁻¹
            = (g ^ b) ^ j * (g ^ b * ι ⟨p, hp⟩ * (g ^ b)⁻¹) * ((g ^ b) ^ j)⁻¹ := by group
          _ = ι ⟨p, hp⟩ := by rw [h4, ih]
    have h5 : g * ι ⟨p, hp⟩ * g⁻¹ = ι ⟨p, hp⟩ := by
      have := h3 c
      rwa [hgbc] at this
    have h6 := hgfpf _ ⟨⟨p, hp⟩, rfl⟩ h5
    have h7 : (⟨p, hp⟩ : ↥(T ⊓ K)) = 1 := hιinj (by rw [h6, map_one])
    exact congrArg Subtype.val h7

end CFSG.GH74.GLS.C3.Layer1.Bk
