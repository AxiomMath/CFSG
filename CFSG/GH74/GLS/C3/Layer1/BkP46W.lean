module

public import CFSG.GH74.GLS.C3.Layer1.BkA5Three
public import CFSG.GH74.GLS.C3.Layer1.BkL114A5
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSylowOf_two_sup_of_odd [Finite G] {R N : Subgroup G} (hR : IsPGroup 2 ↥R)
    (hRN : R ≤ normalizer (N : Set G)) (hN : Odd (Nat.card ↥N)) : IsSylowOf 2 R (R ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : ¬ 2 ∣ Nat.card ↥N := by
    rintro ⟨c, hc⟩
    rw [hc] at hN
    exact (Nat.not_even_iff_odd.2 hN) ⟨c, by ring⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hbot : N ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : orderOf z ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard _ hz.1
    have h2 : orderOf z ∣ Nat.card ↥R := Subgroup.orderOf_dvd_natCard _ hz.2
    rw [hk] at h2
    have hcop : Nat.Coprime (orderOf z) 2 := Nat.coprime_two_right.2 (Odd.of_dvd_nat hN h1)
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) h2
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)
  have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf N R
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left N R hRN, hbot, Subgroup.card_bot,
    mul_one] at h
  have hcard : Nat.card ↥(R ⊔ N) = Nat.card ↥N * Nat.card ↥R := by
    rw [sup_comm]
    exact h
  refine isSylowOf_of_card le_sup_left ?_
  rw [hcard, hk, Nat.factorization_mul (Nat.card_pos).ne' (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  have : (Nat.card ↥N).factorization 2 = 0 := by
    exact Nat.factorization_eq_zero_of_not_dvd hN2
  rw [this]
  simp


theorem frattini_odd [Finite G] {R N : Subgroup G} (hR : IsPGroup 2 ↥R)
    (hRN : R ≤ normalizer (N : Set G)) (hN : Odd (Nat.card ↥N)) {k : G}
    (hk : k ∈ normalizer ((R ⊔ N : Subgroup G) : Set G)) :
    ∃ w ∈ N, w * k ∈ normalizer (R : Set G) := by
  have hS : IsSylowOf 2 R (R ⊔ N) := isSylowOf_two_sup_of_odd hR hRN hN
  have hcjle : Th2.cj k R ≤ R ⊔ N := by
    rintro _ ⟨r, hr, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hk r).1 (Subgroup.mem_sup_left hr)
    simpa [MulAut.conj_apply] using this
  have hcjP : IsPGroup 2 ↥(Th2.cj k R) := hR.map (MulAut.conj k).toMonoidHom
  obtain ⟨g, hgZ, hgR⟩ := Th2.exists_cj_le_of_isSylowOf hS hcjle hcjP
  have hcard : Nat.card ↥R ≤ Nat.card ↥(Th2.cj g (Th2.cj k R)) := by
    unfold Th2.cj
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj k).injective]
  have heq : Th2.cj g (Th2.cj k R) = R := (Subgroup.eq_of_le_of_card_ge hgR hcard)
  have hgk : g * k ∈ normalizer (R : Set G) := by
    refine Th2.mem_normalizer_of_cj_eq ?_
    exact (Stage1.Thm2.Recip.cj_cj g k R).symm.trans heq
  rw [← Subgroup.mem_carrier, show (R ⊔ N : Subgroup G).carrier = ((R ⊔ N : Subgroup G) : Set G) from rfl,
    Subgroup.coe_mul_of_left_le_normalizer_right R N hRN] at hgZ
  obtain ⟨r, hr, w₀, hw₀, rfl⟩ := hgZ
  refine ⟨w₀, hw₀, ?_⟩
  have hrinv : r⁻¹ ∈ normalizer (R : Set G) := Subgroup.le_normalizer (R.inv_mem hr)
  have := (normalizer (R : Set G)).mul_mem hrinv hgk
  simpa [mul_assoc] using this


theorem mem_normalizer_of_conj_le [Finite G] {Z : Subgroup G} {k : G}
    (h : ∀ z ∈ Z, k * z * k⁻¹ ∈ Z) : k ∈ normalizer (Z : Set G) := by
  have hle : Th2.cj k Z ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using h z hz
  have hcard : Nat.card ↥Z ≤ Nat.card ↥(Th2.cj k Z) := by
    unfold Th2.cj
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
  exact Th2.mem_normalizer_of_cj_eq (Subgroup.eq_of_le_of_card_ge hle hcard)

theorem aconfigW_C_le_normalizer [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW n x K T Q S a) : centralizer ({x} : Set G) ≤ normalizer (K : Set G) :=
  fun c hc => mem_normalizer_of_two_sided (fun w hw => h.normalInC c hc w hw) (fun w hw => by
    simpa using h.normalInC c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) w hw)


theorem aconfigW_five_R_le_normalizer_W [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    (T ⊓ K) ⊔ Q ≤ normalizer (pPrimeCoreOf 2 K : Set G) := by
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
  exact fun r hr => TwoThin.mem_normalizer_pPrimeCoreOf (aconfigW_C_le_normalizer h (h.T_le_C (hRT hr)))

theorem aconfigW_five_K_normalizes_sup [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) {k : G} (hk : k ∈ K)
    (hP : ∀ p ∈ T ⊓ K, ∃ p' ∈ T ⊓ K, ∃ w ∈ pPrimeCoreOf 2 K, k * p * k⁻¹ = p' * w) :
    ∀ z ∈ ((T ⊓ K) ⊔ Q) ⊔ pPrimeCoreOf 2 K, k * z * k⁻¹ ∈ ((T ⊓ K) ⊔ Q) ⊔ pPrimeCoreOf 2 K := by
  intro z hz
  have hCD := aconfigW_five_commDisj h
  have hRN := aconfigW_five_R_le_normalizer_W h
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN] at hz
  obtain ⟨r, hr, w₀, hw₀, rfl⟩ := hz
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hCD.comm hr
  obtain ⟨p', hp', w₁, hw₁, hpp'⟩ := hP p hp
  have hkq : k * q * k⁻¹ = ⁅k, q⁆ * q := by
    simp only [commutatorElement_def]
    group
  have hcomm : ⁅k, q⁆ ∈ pPrimeCoreOf 2 K := (h.Q_le_CxK hq).2.2.2 k hk
  have hkw : k * w₀ * k⁻¹ ∈ pPrimeCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.1 (TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hk))
      w₀).1 hw₀
  have e : k * (p * q * w₀) * k⁻¹ = (k * p * k⁻¹) * (k * q * k⁻¹) * (k * w₀ * k⁻¹) := by group
  rw [e, hpp', hkq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left hp')) (Subgroup.mem_sup_right hw₁))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hq)))) (Subgroup.mem_sup_right hkw)


theorem aconfigW_five_w [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
    (h : IsAConfigW 5 x K T Q S a) :
    ∃ w ∈ K, Odd (orderOf w) ∧ w ∈ normalizer ((((T ⊓ K) ⊔ Q : Subgroup G)) : Set G) ∧
      (∀ q ∈ Q, w * q = q * w) ∧ (∀ p ∈ T ⊓ K, w * p * w⁻¹ = p → p = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := h.kbar
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hTC := h.T_le_C
  have hKC := h.K_le_C
  obtain ⟨ψ, hker, hψK⟩ :=
    lemma113d_alt hKC h.normalInC (n := 5) (by norm_num) (by norm_num) e5
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt5 hT2 (aconfigW_inf_sylow h) e5
  obtain ⟨hRel, hRcard⟩ := aconfigW_five_R h
  have hR2 : IsPGroup 2 ↥((T ⊓ K) ⊔ Q) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hWodd : Odd (Nat.card ↥(pPrimeCoreOf 2 K)) := TwoThin.card_pPrimeCoreOf_odd K
  have hRN := aconfigW_five_R_le_normalizer_W h
  have hRT : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left h.Q_le_T
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
    mem_normalizer_of_conj_le (aconfigW_five_K_normalizes_sup h hk₀K hP₀)
  obtain ⟨w₀, hw₀, hnorm⟩ := frattini_odd hR2 hRN hWodd hk₀N
  have hw₀K : w₀ ∈ K := (Setup91.mem_pPrimeCoreOf_iff.1 hw₀).1
  have hwK : w₀ * (k' : G) ∈ K := K.mul_mem hw₀K hk₀K
  have hψw : ψ ⟨w₀ * (k' : G), hKC hwK⟩ = (g : Equiv.Perm (Fin 5)) := by
    have e1 : (⟨w₀ * (k' : G), hKC hwK⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨w₀, hKC hw₀K⟩ * ⟨(k' : G), hKC hk₀K⟩ := rfl
    rw [e1, map_mul, hψW w₀ hw₀K hw₀, hψk₀, one_mul]
  refine ⟨w₀ * (k' : G), hwK, ?_, hnorm, ?_, ?_⟩
  ·
    have hw3 : (w₀ * (k' : G)) ^ 3 ∈ pPrimeCoreOf 2 K := by
      have hw3K : (w₀ * (k' : G)) ^ 3 ∈ K := K.pow_mem hwK 3
      refine hψ1 _ hw3K ?_
      have e1 : (⟨(w₀ * (k' : G)) ^ 3, hKC hw3K⟩ : ↥(centralizer ({x} : Set G))) =
          (⟨w₀ * (k' : G), hKC hwK⟩ : ↥(centralizer ({x} : Set G))) ^ 3 := rfl
      rw [e1, map_pow, hψw]
      have := congrArg (fun z : alternatingGroup (Fin 5) => (z : Equiv.Perm (Fin 5))) hg3
      simpa using this
    have h1 : orderOf ((w₀ * (k' : G)) ^ 3) ∣ Nat.card ↥(pPrimeCoreOf 2 K) :=
      Subgroup.orderOf_dvd_natCard _ hw3
    have hodd3 : Odd (orderOf ((w₀ * (k' : G)) ^ 3)) := Odd.of_dvd_nat hWodd h1
    have h2 : orderOf (w₀ * (k' : G)) ∣ 3 * orderOf ((w₀ * (k' : G)) ^ 3) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact Odd.of_dvd_nat (Odd.mul (by decide) hodd3) h2
  ·
    intro q hq
    have hqR : q ∈ (T ⊓ K) ⊔ Q := Subgroup.mem_sup_right hq
    have hwq1 : (w₀ * (k' : G)) * q * (w₀ * (k' : G))⁻¹ ∈ (T ⊓ K) ⊔ Q :=
      (Subgroup.mem_normalizer_iff.1 hnorm q).1 hqR
    have hNxK : w₀ * (k' : G) ∈ NxK x K := ⟨hKC hwK, Subgroup.le_normalizer hwK⟩
    have hwq2 : (w₀ * (k' : G)) * q * (w₀ * (k' : G))⁻¹ ∈ CxK x K :=
      (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K hNxK) q).1 (h.Q_le_CxK hq)
    have hwq : (w₀ * (k' : G)) * q * (w₀ * (k' : G))⁻¹ ∈ Q := by
      rw [h.hQ]
      exact ⟨hRT hwq1, hwq2⟩
    have hcomm : ⁅w₀ * (k' : G), q⁆ ∈ pPrimeCoreOf 2 K := (h.Q_le_CxK hq).2.2.2 _ hwK
    have hcommQ : ⁅w₀ * (k' : G), q⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hwq (Q.inv_mem hq)
    have hbot := Setup91.inf_pPrimeCoreOf_eq_bot K hT2
    have h1 : ⁅w₀ * (k' : G), q⁆ ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hRT (Subgroup.mem_sup_right hcommQ), hcomm⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
  ·
    intro p hp hwp
    have hpC : p ∈ centralizer ({x} : Set G) := hTC hp.1
    have hwC : w₀ * (k' : G) ∈ centralizer ({x} : Set G) := hKC hwK
    have h1 := hconjψ _ _ hwC hpC
    have hmemC : (w₀ * (k' : G)) * p * (w₀ * (k' : G))⁻¹ ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hwC hpC)
        ((centralizer ({x} : Set G)).inv_mem hwC)
    have h2 : ψ ⟨(w₀ * (k' : G)) * p * (w₀ * (k' : G))⁻¹, hmemC⟩ = ψ ⟨p, hpC⟩ := by
      congr 1
      exact Subtype.ext hwp
    rw [h1, hψw, hψι p hp] at h2
    have h3 : g * ι ⟨p, hp⟩ * g⁻¹ = ι ⟨p, hp⟩ := by
      apply Subtype.ext
      simpa using h2
    have h4 := hgfpf _ ⟨⟨p, hp⟩, rfl⟩ h3
    have h5 : (⟨p, hp⟩ : ↥(T ⊓ K)) = 1 := hιinj (by rw [h4, map_one])
    exact congrArg Subtype.val h5

end CFSG.GH74.GLS.C3.Layer1.Bk
