module

public import CFSG.CGT.M24S.NSTypeA3
public import CFSG.CGT.M24S.NSTypeA

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

theorem card_comap_of_surjective {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    {f : A →* B} (hf : Function.Surjective f) (S : Subgroup B) :
    Nat.card (S.comap f) = Nat.card f.ker * Nat.card S := by
  have h1 := (S.comap f).card_mul_index
  have h2 := S.card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h3
  rw [Subgroup.index_comap_of_surjective S hf] at h1
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, h3, ← h2]
  ring

theorem card_le_of_dvd_384 {G : Type} [Group G] [Finite G] {Q C : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQC : Q ≤ C) (hC : Nat.card C = 384) : Nat.card Q ≤ 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ n ∣ 2 ^ 7 * 3 := by
    rw [← hn, show 2 ^ 7 * 3 = 384 by norm_num, ← hC]
    exact Subgroup.card_dvd_of_le hQC
  rw [hn]
  exact Nat.le_of_dvd (by norm_num)
    ((Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right hdvd)

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

theorem exists_mem_E_commute_dot {x : G} (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀)
    {k : Fin 3 → ZMod 2} (hk : k ≠ 0) :
    ∃ e ∈ c.E, e * x = x * e ∧ top (c.mat e) ⬝ᵥ k = 1 := by
  obtain ⟨u, hu⟩ := exists_dotProduct_eq_one k hk
  obtain ⟨e₁, he₁, he₁m⟩ := c.exists_mem_E u
  have hu₁ : top (c.mat e₁) = u := by rw [he₁m, top_mk4]
  rcases conj_mem_E_eq c he₁ hx with h | h
  · refine ⟨e₁, he₁, ?_, by rw [hu₁]; exact hu⟩
    calc e₁ * x = e₁ * x * e₁⁻¹ * e₁ := by group
      _ = x * e₁ := by rw [h]
  · obtain ⟨s₀, hs₀, hs₀x⟩ := exists_conj_eq_mul_t c hx hxv
    have hs₀E := c.T_le_E hs₀
    refine ⟨e₁ * s₀, c.E.mul_mem he₁ hs₀E, ?_, ?_⟩
    · have h3 : (e₁ * s₀) * x * (e₁ * s₀)⁻¹ = x := by
        calc (e₁ * s₀) * x * (e₁ * s₀)⁻¹ = e₁ * (s₀ * x * s₀⁻¹) * e₁⁻¹ := by group
          _ = e₁ * x * e₁⁻¹ * (e₁ * t * e₁⁻¹) := by rw [hs₀x]; group
          _ = x * t * t := by rw [h, commute_t (c.E_le he₁), mul_inv_cancel_right]
          _ = x := by rw [mul_assoc, ← pow_two, c.z_sq, mul_one]
      calc e₁ * s₀ * x = (e₁ * s₀) * x * (e₁ * s₀)⁻¹ * (e₁ * s₀) := by group
        _ = x * (e₁ * s₀) := by rw [h3]
    · rw [top_mul_of_mem_E c he₁ hs₀E, top_eq_zero_of_mem_T c hs₀, add_zero, hu₁]
      exact hu

@[expose] def uτ : GL (Fin 2) (ZMod 2) := ⟨mb τ₀, mb τ₀, mb_τ₀_sq, mb_τ₀_sq⟩

theorem uτ_ne_one : uτ ≠ 1 := fun h => mb_τ₀_ne_one (congrArg Units.val h)

theorem uτ_sq : uτ ^ 2 = 1 := Units.ext (by rw [pow_two]; exact mb_τ₀_sq)

theorem caseA_coord [Finite G] (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H) {x : G}
    (hx : x ∈ c.E) (hxv : top (c.mat x) = v₀) (hx2 : x ^ 2 = 1) :
    ∃ P : Subgroup G, P ≤ H ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
        Nat.card Q ≤ Nat.card P) ∧ Nat.card P = 2 ^ 7 ∧ SqDerivedEq P t := by
  have hsurj := psi_surjective c hN hns hx hxv hx2
  have hker := ker_psi c hN hns hx hxv hx2
  have hord : Nat.card (Subgroup.zpowers uτ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime uτ_sq uτ_ne_one
  have hle : c.E ⊓ Subgroup.centralizer ({x} : Set G) ≤ H ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ fun e he => c.mem_H_of_mem_E he
  have hkcard : Nat.card (psi c hx hxv).ker = 64 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      card_centralizer_E c hx hxv]
  have hP₀ : Nat.card ((Subgroup.zpowers uτ).comap (psi c hx hxv)) = 128 := by
    rw [card_comap_of_surjective hsurj, hkcard, hord]
  have hPcard : Nat.card (((Subgroup.zpowers uτ).comap (psi c hx hxv)).map
      (H ⊓ Subgroup.centralizer ({x} : Set G)).subtype) = 128 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP₀]
  refine ⟨((Subgroup.zpowers uτ).comap (psi c hx hxv)).map
    (H ⊓ Subgroup.centralizer ({x} : Set G)).subtype, Subgroup.map_subtype_le _,
    fun Q hQ hQC => ?_, by rw [hPcard]; norm_num, ?_, ?_⟩
  · rw [hPcard]
    exact card_le_of_dvd_384 hQ hQC (card_centralizer_eq c hN hns hx hxv hx2)
  · intro y hy
    rw [← Subgroup.map_commutator] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hy₀k : y₀ ∈ (psi c hx hxv).ker := by
      refine (Subgroup.commutator_le.2 fun p hp q hq => ?_) hy₀
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hp)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hq)
      rw [MonoidHom.mem_ker, map_commutatorElement, ← hi, ← hj,
        commutatorElement_eq_one_iff_commute]
      exact Commute.zpow_zpow_self uτ i j
    rw [hker, Subgroup.mem_subgroupOf] at hy₀k
    exact c.sq_eq_one_or_eq_z hy₀k.1
  · obtain ⟨l, hl⟩ := hsurj uτ
    have hlK : StabV₀ c l := stab_of_commute c hx hxv l.2.1 commute_of_mem_cent
    have hmbl : mb (blk (c.mat l)) = mb τ₀ := by rw [← coe_psi c hx hxv l, hl]; rfl
    have hl2 : blk (c.mat l) * blk (c.mat l) = 1 := by
      have h1 : l * l ∈ (psi c hx hxv).ker := by
        rw [MonoidHom.mem_ker, map_mul, hl, ← pow_two, uτ_sq]
      rw [hker, Subgroup.mem_subgroupOf] at h1
      rw [← blk_mul_of_mem c hlK.1 l.2.1]
      exact c.blk_of_mem_E h1.1
    have hl1 : blk (c.mat l) ≠ 1 := fun h => mb_τ₀_ne_one (by rw [← hmbl, h, mb_one])
    obtain ⟨k, f, hk, hfk, hlv⟩ := isLv_of_involution _ hl2 hl1
    have hf : f ≠ 0 := fun hf0 => hl1 (by rw [hlv, hf0, lv, vecMulVec_zero, add_zero])
    obtain ⟨e, he, hex, hek⟩ := exists_mem_E_commute_dot c hx hxv hk
    let e' : ↥(H ⊓ Subgroup.centralizer ({x} : Set G)) :=
      ⟨e, c.mem_H_of_mem_E he, Subgroup.mem_centralizer_singleton_iff.2 hex⟩
    have he' : e' ∈ (Subgroup.zpowers uτ).comap (psi c hx hxv) := by
      rw [Subgroup.mem_comap]
      have h1 : psi c hx hxv e' = 1 := Units.ext (by
        rw [coe_psi]
        change mb (blk (c.mat e)) = 1
        rw [c.blk_of_mem_E he, mb_one])
      rw [h1]
      exact one_mem _
    have hl' : l ∈ (Subgroup.zpowers uτ).comap (psi c hx hxv) := by
      rw [Subgroup.mem_comap, hl]
      exact Subgroup.mem_zpowers uτ
    have hmem := Subgroup.commutator_mem_commutator
      (Subgroup.mem_map.2 ⟨e', he', rfl⟩ : (e : G) ∈ ((Subgroup.zpowers uτ).comap
        (psi c hx hxv)).map (H ⊓ Subgroup.centralizer ({x} : Set G)).subtype)
      (Subgroup.mem_map.2 ⟨l, hl', rfl⟩ : (l : G) ∈ ((Subgroup.zpowers uτ).comap
        (psi c hx hxv)).map (H ⊓ Subgroup.centralizer ({x} : Set G)).subtype)
    rw [commutatorElement_def] at hmem
    exact ⟨_, hmem, sq_commutator_eq_t c hN hns hk hf hfk hlK.1 hlv he hek⟩

theorem exists_coord_of_transvecting (hTH : T ≤ H) (hN : NaturalSL T H 4 1) {t₀ x : G}
    (ht : t₀ ∈ T) (ht1 : t₀ ≠ 1) (hxH : x ∈ H) (hxT : x ∉ T)
    (hxc : CentreTransvecting T t₀ x) :
    ∃ c : NatCoord T H t₀, x ∈ c.E ∧ top (c.mat x) = v₀ := by
  obtain ⟨c₀⟩ := nonempty_natCoord hTH hN ht ht1
  have hxt : x ∈ H ⊓ Subgroup.centralizer ({t₀} : Set G) := by
    refine ⟨hxH, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rcases hxc t₀ ht with h | h
    · calc x * t₀ = x * t₀ * x⁻¹ * t₀⁻¹ * (t₀ * x) := by group
        _ = t₀ * x := by rw [h, one_mul]
    · exfalso
      apply ht1
      have h1 : x * t₀ * x⁻¹ = 1 := by
        calc x * t₀ * x⁻¹ = x * t₀ * x⁻¹ * t₀⁻¹ * t₀ := by group
          _ = t₀ * t₀ := by rw [h]
          _ = 1 := by rw [← pow_two]; exact c₀.z_sq
      calc t₀ = x⁻¹ * (x * t₀ * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
  have hxE : x ∈ c₀.E := mem_E_of_centreTransvecting c₀ hxt hxc
  have ha : top (c₀.mat x) ≠ 0 := fun h => hxT (mem_T_of_top_eq_zero c₀ hxE h)
  exact exists_coord_top c₀ hxE ha

theorem caseA [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 4 1) (hns : ¬ HasComplement T H)
    {t₀ x : G} (ht : t₀ ∈ T) (ht1 : t₀ ≠ 1) (hxH : x ∈ H) (hxT : x ∉ T) (hx2 : x ^ 2 = 1)
    (hxc : CentreTransvecting T t₀ x) :
    ∃ P : Subgroup G, P ≤ H ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ H ⊓ Subgroup.centralizer ({x} : Set G) →
        Nat.card Q ≤ Nat.card P) ∧ Nat.card P = 2 ^ 7 ∧ SqDerivedEq P t₀ := by
  obtain ⟨c, hxE, hxv⟩ := exists_coord_of_transvecting hTH hN ht ht1 hxH hxT hxc
  exact caseA_coord c hN hns hxE hxv hx2

end CFSG.CGT.M24S.NSB
