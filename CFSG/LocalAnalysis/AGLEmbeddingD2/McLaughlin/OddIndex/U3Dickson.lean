module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3DicksonPrep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.PSL2Dichotomy
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2Strong

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

section Generic

theorem false_of_comm {G : Type*} [Group G] {a s : G} (ha : orderOf a = 3)
    (hs : s * a * s⁻¹ = a⁻¹) (hc : s * a = a * s) : False := by
  rw [hc, mul_inv_cancel_right] at hs
  have h2 : a ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hs
  have := orderOf_dvd_of_pow_eq_one h2
  rw [ha] at this
  norm_num at this

theorem false_of_borel {H : Type*} [Group H] [Finite H] {p m : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {NB CB : Subgroup H} (hNn : NB.Normal) (hNcard : Nat.card NB = p ^ m) (hCc : IsCyclic CB)
    (hsup : NB ⊔ CB = ⊤) {a s : H} (ha : orderOf a = 3) (hs : s * a * s⁻¹ = a⁻¹) : False := by
  have hp : p.Prime := Fact.out
  have hsurj : Function.Surjective ((QuotientGroup.mk' NB).comp CB.subtype) := by
    have hNb : NB.map (QuotientGroup.mk' NB) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hmapC : CB.map (QuotientGroup.mk' NB) = ⊤ := by
      have h1 := Subgroup.map_sup NB CB (QuotientGroup.mk' NB)
      rw [hsup, hNb, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective NB)] at h1
      exact h1.symm
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmapC
  have hcomm : ∀ u v : H ⧸ NB, u * v = v * u := by
    intro u v
    obtain ⟨c₁, rfl⟩ := hsurj u
    obtain ⟨c₂, rfl⟩ := hsurj v
    have h := congrArg (QuotientGroup.mk' NB) (congrArg Subtype.val (hCc.commGroup.mul_comm c₁ c₂))
    simpa [map_mul] using h
  set π := QuotientGroup.mk' NB with hπ
  have e1 : π s * π a * (π s)⁻¹ = π a⁻¹ := by
    rw [← hs]
    simp [map_mul, map_inv]
  rw [hcomm (π s) (π a), mul_inv_cancel_right, map_inv] at e1
  have h2 : π (a ^ 2) = 1 := by
    rw [pow_two, map_mul]
    exact mul_eq_one_iff_eq_inv.mpr e1
  have ha2 : a ^ 2 ∈ NB := (QuotientGroup.eq_one_iff _).mp h2
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  have haN : a ∈ NB := by
    have : a = (a ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ']
      exact ha3
    rw [this]
    exact NB.inv_mem ha2
  have hdvd : orderOf a ∣ p ^ m := hNcard ▸ Subgroup.orderOf_dvd_natCard NB haN
  rw [ha] at hdvd
  have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow hdvd
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p).symm

end Generic

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem exists_inverting (hF : Nat.card K = p ^ f) (hp3 : p ≠ 3)
    (hq3 : Nat.card K % 3 = 1) {A : Subgroup (PSL2MatrixGroup K)} (hA : Nat.card A = 3) :
    ∃ a ∈ A, ∃ s ∈ Subgroup.normalizer (A : Set (PSL2MatrixGroup K)),
      orderOf a = 3 ∧ s * a * s⁻¹ = a⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw3, hw1⟩ := exists_cube_root_unity (K := K) hq3
  set a₀ : PSL2MatrixGroup K := projPSL K (dSLu w) with ha₀
  set s₀ : PSL2MatrixGroup K := projPSL K swSL with hs₀
  have ha₀o : orderOf a₀ = 3 := orderOf_projPSL_dSLu hw3 hw1
  have hconj₀ : s₀ * a₀ * s₀⁻¹ = a₀⁻¹ := projPSL_swSL_conj w
  have hA' : Nat.card (Subgroup.zpowers a₀) = 3 := by rw [Nat.card_zpowers, ha₀o]
  obtain ⟨g, hg⟩ := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj.exists_conj_eq_of_card_three
    (isCyclic_of_isPGroup_three hF hp3) hA hA'
  have hmem : ∀ y ∈ Subgroup.zpowers a₀, g * y * g⁻¹ ∈ A := by
    intro y hy
    rw [← hg]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hmem' : ∀ n ∈ A, ∃ y ∈ Subgroup.zpowers a₀, n = g * y * g⁻¹ := by
    intro n hn
    rw [← hg] at hn
    obtain ⟨y, hy, rfl⟩ := hn
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  refine ⟨g * a₀ * g⁻¹, hmem _ (Subgroup.mem_zpowers _), g * s₀ * g⁻¹, ?_, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨y, hy, rfl⟩ := hmem' n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : g * s₀ * g⁻¹ * (g * a₀ ^ k * g⁻¹) * (g * s₀ * g⁻¹)⁻¹ =
        g * (a₀⁻¹) ^ k * g⁻¹ := by
      rw [← hconj₀, conj_zpow]
      group
    rw [this]
    exact hmem _ (Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _)
  · have := MulEquiv.orderOf_eq (MulAut.conj g) a₀
    simpa [MulAut.conj_apply, ha₀o] using this
  · calc g * s₀ * g⁻¹ * (g * a₀ * g⁻¹) * (g * s₀ * g⁻¹)⁻¹ = g * (s₀ * a₀ * s₀⁻¹) * g⁻¹ := by group
      _ = g * a₀⁻¹ * g⁻¹ := by rw [hconj₀]
      _ = (g * a₀ * g⁻¹)⁻¹ := by group

theorem psl2_normalizer_three_dichotomy
    (hK : Nat.card K = p ^ f) (hq3 : Nat.card K % 3 = 1) (hq4 : Nat.card K % 4 = 3)
    {A H : Subgroup (PSL2MatrixGroup K)} (hA : Nat.card A = 3)
    (hAH : Subgroup.normalizer (A : Set (PSL2MatrixGroup K)) ≤ H) :
    H = Subgroup.normalizer (A : Set (PSL2MatrixGroup K)) ∨ ¬ 2 ∣ H.index := by
  have hp : p.Prime := Fact.out
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hK
  have hq7 : 7 ≤ Nat.card K := by omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ Nat.card K := hK ▸ dvd_pow_self 3 hf0
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ Nat.card K := hK ▸ dvd_pow_self 2 hf0
    omega
  set N : Subgroup (PSL2MatrixGroup K) := Subgroup.normalizer (A : Set (PSL2MatrixGroup K)) with hN
  have hAN : A ≤ N := Subgroup.le_normalizer
  obtain ⟨a, haA, s, hsN, hao, hsa⟩ := exists_inverting hK hp3 hq3 hA
  have haH : a ∈ H := hAH (hAN haA)
  have hsH : s ∈ H := hAH hsN
  have hsa_not : ¬ s * a = a * s := fun hc => false_of_comm hao hsa hc
  obtain ⟨z, g, t, hz3, hg0, hg2, hzg, ht⟩ := exists_torus_element hK hp3
  have hzg' : z * g = Nat.card K - 1 := by
    rcases hzg with h | h
    · exact h
    · exfalso
      have h3 : 3 ∣ z * g := Dvd.dvd.mul_right hz3 g
      rw [h] at h3
      omega
  obtain ⟨x, hxo, hxc⟩ := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj.exists_conj_mem_centralizer
    (isCyclic_of_isPGroup_three hK hp3) hA (t := t) (by rw [ht]; exact hz3)
  have hxN : x ∈ N := Subgroup.centralizer_le_normalizer (A : Set (PSL2MatrixGroup K)) hxc
  have hxH : x ∈ H := hAH hxN
  have hxo' : orderOf x = z := hxo.trans ht
  have hxoH : orderOf (⟨x, hxH⟩ : H) = z := (Subgroup.orderOf_coe ⟨x, hxH⟩).symm.trans hxo'
  have hzq : Nat.card K ≤ 2 * z + 1 := by
    have : z * g ≤ z * 2 := Nat.mul_le_mul_left z hg2
    omega
  have hNcard : Nat.card K - 1 ≤ Nat.card N := by
    set C : Subgroup (PSL2MatrixGroup K) := Subgroup.centralizer (A : Set (PSL2MatrixGroup K)) with hC
    have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (A : Set (PSL2MatrixGroup K))
    have hxz : Nat.card (Subgroup.zpowers x) = z := by rw [Nat.card_zpowers, hxo']
    have hzC : z ≤ Nat.card C := by
      have hle : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr hxc
      have := Subgroup.card_le_of_le hle
      omega
    have hCne : Nat.card C ≠ Nat.card N := by
      intro heq
      have hCeq : C = N := Subgroup.eq_of_le_of_card_ge hCN (le_of_eq heq.symm)
      apply hsa_not
      have hsC : s ∈ C := hCeq ▸ hsN
      exact (Subgroup.mem_centralizer_iff.mp hsC a haA).symm
    have hdvd : Nat.card C ∣ Nat.card N := Subgroup.card_dvd_of_le hCN
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · have : 0 < Nat.card N := Nat.card_pos
        omega
      · exact absurd (by simpa using hk.symm) hCne
      · omega
    have : 2 * Nat.card C ≤ Nat.card N := by rw [hk]; nlinarith
    omega
  have hNH : Nat.card N ∣ Nat.card H := Subgroup.card_dvd_of_le hAH
  have hq2 : (Nat.card K) ^ 2 = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hpsl : Nat.card (PSL2MatrixGroup K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    have := MaxUp.card_psl2_odd hK hp2
    rwa [← hK] at this
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hK H with
    hE | ⟨z', -, -, hC⟩ | ⟨z', hz'd, hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, ⟨e⟩⟩ | ⟨h5a, ⟨e⟩⟩ |
    ⟨m, t', -, -, NB, CB, hNn, hNe, hNcard', hCc, -, -, hsup⟩ | ⟨m, hm0, hmf, ⟨e⟩, -⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, -⟩
  · exact (hsa_not (congrArg Subtype.val (hE.is_comm.comm ⟨s, hsH⟩ ⟨a, haH⟩))).elim
  · exact (hsa_not (congrArg Subtype.val (hC.commGroup.mul_comm ⟨s, hsH⟩ ⟨a, haH⟩))).elim
  ·
    left
    have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := Nat.gcd_eq_right (by omega)
    rw [hgcd] at hz'd
    have hz'le : z' ≤ (Nat.card K + 1) / 2 := by
      rcases hz'd with h | h
      · exact (Nat.le_of_dvd (by omega) h).trans (Nat.div_le_div_right (by omega))
      · exact Nat.le_of_dvd (by omega) h
    have hH2 : Nat.card H = 2 * z' := hcard
    have hHle : Nat.card H ≤ Nat.card K + 1 := by omega
    obtain ⟨k, hk⟩ := hNH
    have hk1 : k = 1 := by
      rcases k with _ | _ | k
      · have : 0 < Nat.card H := Nat.card_pos
        omega
      · rfl
      · exfalso
        have : 2 * Nat.card N ≤ Nat.card H := by rw [hk]; nlinarith
        omega
    subst hk1
    exact (Subgroup.eq_of_le_of_card_ge hAH (by omega)).symm
  ·
    exfalso
    have ha3 : a ^ 3 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [hao] at this
    have hsa2 : s * a * s⁻¹ = a ^ 2 := by
      rw [hsa, inv_eq_iff_mul_eq_one, ← pow_succ']
      exact ha3
    have h3 := a4_normalizer (e ⟨a, haH⟩) (e ⟨s, hsH⟩)
      (by rw [← map_pow]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext ha3))
      (fun h => by
        have : a = 1 := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
        rw [this, orderOf_one] at hao
        omega)
      (Or.inr (by
        rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext hsa2)))
    apply hsa_not
    rcases h3 with h | h | h
    · have := congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
      rw [show s = 1 from this]
      simp
    · have := congrArg Subtype.val (e.injective h)
      rw [show s = a from this]
    · have := congrArg Subtype.val (e.injective (h.trans (map_pow e _ 2).symm))
      rw [show s = a ^ 2 from this]
      exact (Commute.pow_left (Commute.refl a) 2).eq
  ·
    have hH24 : Nat.card H = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm]
      simp [Nat.factorial]
    have hle24 : Nat.card N ≤ 24 := hH24 ▸ Nat.le_of_dvd Nat.card_pos hNH
    have hq : Nat.card K = 7 ∨ Nat.card K = 19 := by omega
    rcases hq with hq | hq
    · right
      have hidx := Subgroup.card_mul_index H
      rw [hpsl, hq, hH24] at hidx
      norm_num at hidx
      omega
    · exfalso
      have h16' : 16 ∣ Nat.card K ^ 2 - 1 := by rw [hq2]; exact h16
      rw [hq] at h16'
      norm_num at h16'
  ·
    exfalso
    have h35 := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_alternating_five
      e ⟨x, hxH⟩
    rw [hxoH] at h35
    have hz3' : z = 3 := by
      rcases h35 with h | h | h
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
      · exact Nat.dvd_antisymm h hz3
      · exact absurd (Nat.dvd_trans hz3 h) (by norm_num)
    have hq : Nat.card K = 7 := by
      subst hz3'
      interval_cases g <;> omega
    rcases h5a with h5 | h5
    · have h4 : (5 ^ f) % 4 = 1 := by rw [Nat.pow_mod]; norm_num
      rw [h5] at hK
      omega
    · rw [← hq2, hq] at h5
      norm_num at h5
  ·
    exfalso
    exact false_of_borel hp3 hNn hNcard' hCc hsup (a := ⟨a, haH⟩) (s := ⟨s, hsH⟩)
      ((Subgroup.orderOf_coe ⟨a, haH⟩).symm.trans hao) (Subtype.ext (by simpa using hsa))
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have h2 : p ^ m ≠ 2 := by
      intro h
      have : p ∣ 2 := h ▸ dvd_pow_self p hm0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have ha := four_le_pow hp3 hm0 h2
    by_cases hmeq : m = f
    · right
      obtain ⟨φ⟩ := nonempty_galoisField_ringHom hK hmf
      have hcardle : Nat.card K ≤ Nat.card (GaloisField p m) := by rw [hK, hGF, hmeq]
      have hbij := φ.injective.bijective_of_nat_card_le hcardle
      let ψ : K ≃+* GaloisField p m := (RingEquiv.ofBijective φ hbij).symm
      have hle : Nat.card (PSL2MatrixGroup K) ≤ Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_le_card_of_injective _ (psl2Map_injective ψ.toRingHom)
      have htop : H = ⊤ := by
        refine Subgroup.eq_top_of_card_eq H ?_
        refine le_antisymm (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card H)) ?_
        rw [Nat.card_congr e.toEquiv]
        exact hle
      rw [htop, Subgroup.index_top]
      exact fun h => by omega
    · exfalso
      obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> simp_all
        · exact h
      have hf2 : 2 * m ≤ f := by nlinarith
      have hpow : (p ^ m) ^ 2 ≤ Nat.card K := by
        rw [hK, ← pow_mul, mul_comm]
        exact Nat.pow_le_pow_right hp.pos hf2
      have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le
        (GaloisField p m) (e ⟨x, hxH⟩)
      rw [MulEquiv.orderOf_eq, hxoH, hGF] at hord
      exact false_of_subfield_bound ha hord hpow hzq
  ·
    exfalso
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have h2 : p ^ m ≠ 2 := by
      intro h
      have : p ∣ 2 := h ▸ dvd_pow_self p hm0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have hf2 : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    have ha := four_le_pow hp3 hm0 h2
    have hpow : (p ^ m) ^ 2 ≤ Nat.card K := by
      rw [hK, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right hp.pos hf2
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le
      (GaloisField p m) (e ⟨x, hxH⟩)
    rw [MulEquiv.orderOf_eq, hxoH, hGF] at hord
    exact false_of_subfield_bound ha hord hpow hzq

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
