module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sh
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29C
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Se
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sf
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup CFSG.ComponentClassification.UnbalancedLayer

namespace Model

variable {P : Type} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

@[expose] def Concl (ι : P) (J T' : Subgroup P) (t : P) : Prop :=
  (T' ⊓ J) ⊓ conjugate (T' ⊓ J) t = ⊥ ∧
    (∀ d ∈ T' ⊓ J, ∀ e ∈ conjugate (T' ⊓ J) t, d * e = e * d) ∧
    (T' ⊓ J) ⊔ conjugate (T' ⊓ J) t = T' ∧
    (conjugate (T' ⊓ J) t ⊓ centralizer (J : Set P)).relIndex (conjugate (T' ⊓ J) t) = 4 ∧
    ι ∈ conjugate (T' ⊓ J) t ⊓ centralizer (J : Set P) ∧
    (∀ e ∈ conjugate (T' ⊓ J) t, ι * e = e * ι) ∧
    IsCyclic ↥(conjugate (T' ⊓ J) t ⊓ centralizer (J : Set P)) ∧
    IsCyclic ↥(T' ⊓ centralizer (J : Set P)) ∧
    2 * Nat.card ↥(T' ⊓ centralizer (J : Set P)) = Nat.card ↥(T' ⊓ J)

theorem conj_iota_eq_z₁ {t : P} (htL : t ∈ L) (htN : t ∈ normalizer (M.T : Set P))
    (htC : t ∉ centralizer ({ι} : Set P)) : t⁻¹ * ι * t = M.z₁ := by
  have hmem : t⁻¹ * ι * t ∈ M.T := by
    have := (mem_normalizer_iff.mp (inv_mem htN) ι).mp M.iota_mem_T
    rwa [inv_inv] at this
  have hc : ∀ y ∈ M.T, t⁻¹ * ι * t * y = y * (t⁻¹ * ι * t) := by
    intro y hy
    have hy' : t * y * t⁻¹ ∈ M.T := (mem_normalizer_iff.mp htN y).mp hy
    have h1 := mem_centralizer_singleton_iff.mp (M.T_le hy').1
    calc t⁻¹ * ι * t * y = t⁻¹ * (ι * (t * y * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * y * t⁻¹) * ι) * t := by rw [h1]
      _ = y * (t⁻¹ * ι * t) := by group
  rcases M.mem_T_of_comm hmem hc with h | h | h | h
  · exfalso
    apply M.iota_ne
    have := congrArg (fun x => t * x * t⁻¹) h
    simpa [mul_assoc] using this
  · exact h
  · exfalso
    apply htC
    rw [mem_centralizer_singleton_iff]
    have := congrArg (fun x => t * x) h
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at this
    exact this.symm
  · exfalso
    apply M.not_conj t⁻¹ (inv_mem htL)
    rw [inv_inv, h]
    exact (M.iota_comm_z₁).symm

theorem concl_T [Finite P] {t : P} (htL : t ∈ L) (htN : t ∈ normalizer (M.T : Set P))
    (htC : t ∉ centralizer ({ι} : Set P)) : Concl ι J M.T t := by
  have hz := M.conj_iota_eq_z₁ htL htN htC
  set x := t * M.t₀⁻¹ with hx
  have hxC : x⁻¹ ∈ centralizer ({ι} : Set P) ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      inv_mem (mul_mem htL (inv_mem M.t₀_mem))⟩
    have h1 : M.t₀ * M.z₁ * M.t₀⁻¹ = ι := by
      have := M.t₀_conj_iota
      rw [← this]
      group
    calc x⁻¹ * ι = M.t₀ * (t⁻¹ * ι * t) * M.t₀⁻¹ * x⁻¹ := by rw [hx]; group
      _ = M.t₀ * M.z₁ * M.t₀⁻¹ * x⁻¹ := by rw [hz]
      _ = ι * x⁻¹ := by rw [h1]
  have hxN : x⁻¹ ∈ normalizer (M.T : Set P) := by
    rw [hx, _root_.mul_inv_rev, inv_inv]
    exact mul_mem M.t₀_mem_normalizer (inv_mem htN)
  unfold Concl
  rw [M.T_inf_J]
  have hD : conjugate M.D₁ t = M.D₂ := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rw [mem_conjugate_iff] at hy
      rw [M.D₂_eq, mem_conjugate_iff]
      have hJ : x⁻¹ * (t * y * t⁻¹) * x⁻¹⁻¹ ∈ J :=
        (M.normJ _ hxC _).mp (by obtain ⟨a, ha⟩ := hy; rw [← ha]; exact M.le_J a)
      have hT : x⁻¹ * (t * y * t⁻¹) * x⁻¹⁻¹ ∈ M.T :=
        (mem_normalizer_iff.mp hxN _).mp (M.D₁_le_T hy)
      have h1 : x⁻¹ * (t * y * t⁻¹) * x⁻¹⁻¹ ∈ M.T ⊓ J := ⟨hT, hJ⟩
      rw [M.T_inf_J] at h1
      convert h1 using 1
      rw [hx]
      group
    · rw [M.card_D₂, conjugate, Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective,
        M.card_D₁]
  rw [hD]
  refine ⟨M.inf_D_eq_bot, ?_, M.sup_D_eq_T, ?_, ⟨M.iota_mem_D₂, M.iota_mem_cent⟩, ?_,
    M.isCyclic_D₂_inf_cent, M.isCyclic_T_inf_cent, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact M.comm₁₂ a b
  · have h1 := Subgroup.relIndex_mul_card (M.D₂ ⊓ centralizer (J : Set P)) M.D₂
    rw [inf_right_comm, inf_idem, M.card_D₂_inf_cent, M.card_D₂] at h1
    have e : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
      have := M.two_le
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
      ring
    rw [e] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos (m - 1)) h1
  · rintro _ ⟨b, rfl⟩
    exact M.iota_comm₂ b
  · rw [M.card_T_inf_cent, M.card_D₁, pow_succ, mul_comm]

include M in
theorem concl [Finite P] {T' : Subgroup P}
    (hT' : Seven.IsSylowIn T' (centralizer ({ι} : Set P) ⊓ L)) {t : P} (htL : t ∈ L)
    (htN : t ∈ normalizer (T' : Set P)) (htC : t ∉ centralizer ({ι} : Set P)) :
    Concl ι J T' t := by
  obtain ⟨c, hc, hT⟩ := exists_conj_of_isSylowIn M.isSylowIn_T hT'
  have hT'' : T' = (M.conj hc).T := by rw [T_conj, hT]
  rw [hT''] at htN ⊢
  exact (M.conj hc).concl_T htL htN htC

end Model

theorem isSylowIn_inf_normal {X : Type} [Group X] [Finite X] {R M N : Subgroup X}
    (h : Seven.IsSylowIn R M) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set X)) :
    Seven.IsSylowIn (R ⊓ N) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRM, R', hR'⟩ := h
  have hn : (N.subgroupOf M).Normal := by
    constructor
    intro n hn m
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hMN m.2) n).mp hn
    simpa using this
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal R' (N := N.subgroupOf M)
  let e : ↥((N.subgroupOf M)) ≃* ↥N := subgroupOfEquivOfLe hNM
  have hsurj : Function.Surjective (e.toMonoidHom : ↥(N.subgroupOf M) →* ↥N) := by
    rw [MulEquiv.coe_toMonoidHom]; exact e.surjective
  refine ⟨inf_le_right, Q.mapSurjective hsurj, ?_⟩
  rw [Sylow.coe_mapSurjective, hQ, hR']
  ext w
  simp only [mem_map, mem_subgroupOf, mem_inf]
  constructor
  · rintro ⟨v, ⟨hv1, -⟩, rfl⟩
    exact ⟨hv1, (e v).2⟩
  · rintro ⟨hw1, hw2⟩
    refine ⟨e.symm w, ⟨?_, ?_⟩, by simp⟩
    · exact hw1
    · exact (e.symm w).2

theorem prop29ConclCorr_of_model {H : Type} [Group H] [Finite H] [(generalizedFitting H).Normal]
    {ι : H} {J₁ S₁ : Subgroup H} {m : ℕ} (M : Model (generalizedFitting H) ι J₁ m)
    (hO : pPrimeCore 2 ↥J₁ = ⊥) (hS : Seven.IsSylowIn S₁ (centralizer ({ι} : Set H))) :
    Prop29ConclCorr H ι J₁ S₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := generalizedFitting H with hLdef
  set T := S₁ ⊓ L with hTdef
  have hCL : centralizer ({ι} : Set H) ⊓ L ≤ centralizer ({ι} : Set H) := inf_le_left
  have hCN : centralizer ({ι} : Set H) ≤ normalizer ((centralizer ({ι} : Set H) ⊓ L : Subgroup H) :
      Set H) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hx1) (inv_mem hg),
        (inferInstance : L.Normal).conj_mem x hx2 g⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [e]; exact mul_mem (mul_mem (inv_mem hg) hx1) hg
      · have := (inferInstance : L.Normal).conj_mem _ hx2 g⁻¹
        rwa [inv_inv, ← e] at this
  have hT0 := isSylowIn_inf_normal hS hCL hCN
  have hTe : S₁ ⊓ (centralizer ({ι} : Set H) ⊓ L) = T := by
    rw [hTdef, ← inf_assoc, inf_of_le_left hS.1]
  rw [hTe] at hT0
  have hT : Seven.IsSylowIn T (centralizer ({ι} : Set H) ⊓ L) := hT0
  obtain ⟨c, -, hcT⟩ := exists_conj_of_isSylowIn M.isSylowIn_T hT
  have hcard : Nat.card ↥(S₁ ⊓ L) = 2 ^ (2 * m + 2) := by
    rw [← hTdef, hcT, Subgroup.card_map_of_injective (MulAut.conj c).injective, M.card_T]
  obtain ⟨t, htL, htN, htS, htt⟩ := exists_t (L := L) (Seven.IsSylowIn.isPGroup hS) hcard
    M.dvd_L M.not_dvd_L
  have htC : t ∉ centralizer ({ι} : Set H) := by
    intro htC
    have h2 : IsPGroup 2 (zpowers t) := by
      obtain ⟨k, hk⟩ := (Seven.IsSylowIn.isPGroup hS) ⟨t * t, htt⟩
      have h3 : t ^ 2 ^ (k + 1) = 1 := by
        have := congrArg Subtype.val hk
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        rw [pow_succ', pow_mul, _root_.sq]
        exact this
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h3)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have h1 : IsPGroup 2 ↥(zpowers t ⊔ S₁) :=
      IsPGroup.to_sup_of_normal_right' h2 (Seven.IsSylowIn.isPGroup hS)
        (zpowers_le.mpr htN)
    have h4 : zpowers t ⊔ S₁ ≤ centralizer ({ι} : Set H) := sup_le (zpowers_le.mpr htC) hS.1
    have h5 := eq_of_isSylowIn hS h4 h1 le_sup_right
    exact htS (h5 ▸ mem_sup_left (mem_zpowers t))
  have htNT : t ∈ normalizer (T : Set H) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp htN x).mp hx1,
        (inferInstance : L.Normal).conj_mem x hx2 t⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp htN x).mpr hx1, ?_⟩
      have := (inferInstance : L.Normal).conj_mem _ hx2 t⁻¹
      rwa [inv_inv, ← e] at this
  obtain ⟨hbot, hcomm, hsup, hidx, hι, hιc, hcyc, hcyc2, hcard2⟩ := Model.concl M hT htL htNT htC
  have hK := kernel_eq_centralizer hO
  have hSJ : S₁ ⊓ J₁ = T ⊓ J₁ := by
    rw [hTdef, inf_assoc, inf_of_le_right M.J_le_L]
  refine ⟨t, htL, htN, htS, htt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun d _ hd j hj => outer_of_not_mem hO hd j hj⟩
  · rw [hSJ]; exact hbot
  · rw [hSJ]; exact hcomm
  · rw [hSJ]; exact hsup
  · rw [hSJ, hK]; exact hidx
  · rw [hSJ, hK]; exact hι
  · rw [hSJ]; exact hιc
  · rw [hSJ, hK]; exact hcyc
  · rw [hK]; exact hcyc2
  · rw [hK, hSJ]; exact hcard2

end CFSG.ComponentClassification.GSThmB.P29
