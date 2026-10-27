module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4O8C
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTwoA
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4O8B
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckD
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.EvenSmallLie.OmegaEight

namespace E4

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_of_isSubnormal {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B) :
    pCoreOf 2 A ≤ pCoreOf 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction h with
  | refl A => exact le_rfl
  | @step A M B hAM hn _ ih =>
    refine le_trans ?_ ih
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 A).trans hAM) ?_ (LieType.BorelTits.pCoreOf_isPGroup 2 A)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)

theorem isPGroup_comm {Δ : Set (Subgroup G)} (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ)
    {K : Subgroup G} (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) (h2 : IsPGroup 2 ↥K)
    {j m : G} (hj : j ∈ K) (hm : m * z = z * m) (k : ℕ) :
    ∃ a : ℕ, ((j⁻¹ * m * j * m⁻¹) ^ k) ^ (2 ^ a) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G)
  set P := pCoreOf 2 C
  have hKP : K ≤ P := (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
    (Subgroup.le_normalizer) h2).trans (pCoreOf_le_of_isSubnormal (h.isSubnormal_centralizer hK hz))
  have hmC : m ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hm
  have hmN : m ∈ Subgroup.normalizer (P : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C (Subgroup.le_normalizer hmC)
  have hjP := hKP hj
  have hx : j⁻¹ * m * j * m⁻¹ ∈ P := by
    have h1 : m * j * m⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hmN j).mp hjP
    have h2 := P.mul_mem (P.inv_mem hjP) h1
    rwa [show j⁻¹ * (m * j * m⁻¹) = j⁻¹ * m * j * m⁻¹ by group] at h2
  obtain ⟨a, ha⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 C ⟨_, P.pow_mem hx k⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem exists_inner_four {N K : Subgroup G} [N.Normal] (hidx : N.index ∣ 6)
    (eK : ↥K ≃* QuaternionGroup 2) (z : G) :
    ∃ u ∈ K, u ∈ N ∧ u ≠ 1 ∧ u ≠ z := by
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hr := N.relIndex_mul_card K
  have hr6 : N.relIndex K ∣ 6 := (Subgroup.relIndex_dvd_index_of_normal N K).trans hidx
  have hr8 : N.relIndex K ∣ 8 := h8 ▸ Subgroup.relIndex_dvd_card N K
  have hr2 : N.relIndex K ∣ 2 := by
    have := Nat.dvd_gcd hr6 hr8
    norm_num at this
    exact this
  have hpos : 0 < N.relIndex K := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hr2; norm_num at hr2)
  have hle2 : N.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) hr2
  have hcard : 4 ≤ Nat.card ↥(N ⊓ K) := by
    rw [h8] at hr
    by_contra hlt
    rw [not_le] at hlt
    have : N.relIndex K * Nat.card ↥(N ⊓ K) < 8 := by
      calc N.relIndex K * Nat.card ↥(N ⊓ K) ≤ 2 * Nat.card ↥(N ⊓ K) :=
            Nat.mul_le_mul_right _ hle2
        _ < 8 := by omega
    omega
  by_contra hno
  simp only [not_exists, not_and, ne_eq, not_not] at hno
  have hsub : ((N ⊓ K : Subgroup G) : Set G) ⊆ {1, z} := by
    intro u hu
    obtain ⟨huN, huK⟩ := hu
    by_cases h1 : u = 1
    · exact Or.inl h1
    · exact Or.inr (hno u huK huN h1)
  have hle : Nat.card ↥(N ⊓ K) ≤ 2 := by
    have h1 : Nat.card ↥(N ⊓ K) = ((N ⊓ K : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
    rw [h1]
    calc ((N ⊓ K : Subgroup G) : Set G).ncard ≤ ({1, z} : Set G).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({z} : Set G).ncard + 1 := Set.ncard_insert_le 1 {z}
      _ = 2 := by rw [Set.ncard_singleton]
  omega


theorem le_of_mem {N : Subgroup G} [N.Normal] (e : ↥N ≃* ↥omegaT)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {Δ : Set (Subgroup G)}
    (h : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ)
    (hθ : ∀ z : G, orderOf z = 2 → oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥)
    {K : Subgroup G} (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) (hzN : z ∈ N) :
    K ≤ N := by
  have hd := ambientQuatDatum_of_mem h hθ hK hz
  obtain ⟨eK⟩ := hd.q8
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  intro j hj
  by_contra hjN
  obtain ⟨u, huK, huN, hu1, huz⟩ := exists_inner_four (index_dvd_six e hC) eK z
  have huu : u * u = z := q8_sq eK hz huK hu1 huz
  have hjj : j * j = z := q8_sq eK hz hj (fun h1 => hjN (h1 ▸ N.one_mem))
    (fun h1 => hjN (h1 ▸ hzN))
  have hu2 : u * u ≠ 1 := huu ▸ hz.ne_one
  have hinv : j * u * j⁻¹ = u⁻¹ := by
    rcases E4C.comm_or_inv_of_q8 eK huK hj hu2 with hc | hc
    · exfalso
      rcases mem_zpowers_of_comm eK huK hj hu2 hc with h1 | h1 | h1 | h1 <;> apply hjN <;>
        rw [h1]
      · exact N.one_mem
      · exact huN
      · exact N.mul_mem huN huN
      · exact N.mul_mem (N.mul_mem huN huN) huN
    · exact hc
  have hφ := phi_injective e hC
  have hzO : phi e z ∈ omegaT := phi_mem_omegaT_of_mem e hzN
  have hz2 : orderOf (phi e z) = 2 := by
    rw [orderOf_injective (phi e) hφ z]
    exact orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  obtain ⟨i, hi, a, ha, hza⟩ := O8.exists_conj_main hzO hz2
  set ψ : G →* Equiv.Perm (Fin 360) := (MulAut.conj a⁻¹).toMonoidHom.comp (phi e) with hψ
  have hψa : ∀ g, ψ g = a⁻¹ * phi e g * a := fun g => by
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hψinj : Function.Injective ψ := (MulAut.conj a⁻¹).injective.comp hφ
  have hψO : ∀ g, ψ g ∈ omegaT ↔ g ∈ N := fun g => by
    rw [hψa]
    constructor
    · intro hg
      refine mem_of_phi_mem e hC ?_
      have h1 := (conj_mem_omegaT ha).1 hg
      rwa [show a * (a⁻¹ * phi e g * a) * a⁻¹ = phi e g by group] at h1
    · intro hg
      have h1 := (conj_mem_omegaT (autT.inv_mem ha)).1 (phi_mem_omegaT_of_mem e hg)
      rwa [inv_inv] at h1
  have hψz : ψ z = mainPerm i := by
    rw [hψa, hza]
    group
  have hjA : ψ j ∈ autT := by
    rw [hψa]
    exact autT.mul_mem (autT.mul_mem (autT.inv_mem ha) (phi_mem_autT e j)) ha
  have hjO : ψ j ∉ omegaT := fun h1 => hjN ((hψO j).1 h1)
  have hjj' : ψ j * ψ j = mainPerm i := by rw [← map_mul, hjj, hψz]
  rcases E4O8.outer_root_spec hi hjA hjO hjj' with ⟨c, hcO, hcx, k, hk1, hk3⟩ | hno
  ·
    obtain ⟨m, hm⟩ : ∃ m : G, ψ m = c := by
      obtain ⟨m, hm⟩ := exists_of_mem_omegaT e ((conj_mem_omegaT ha).1 hcO)
      refine ⟨m, ?_⟩
      rw [hψa, hm]
      group
    have hmz : m * z = z * m := hψinj (by rw [map_mul, map_mul, hm, hψz, hcx])
    obtain ⟨b, hb⟩ := isPGroup_comm h hK hz h2 hj hmz k
    have hψx : ψ ((j⁻¹ * m * j * m⁻¹) ^ k) = ((ψ j)⁻¹ * c * ψ j * c⁻¹) ^ k := by
      rw [map_pow, map_mul, map_mul, map_mul, map_inv, map_inv, hm]
    have hg2 : (((ψ j)⁻¹ * c * ψ j * c⁻¹) ^ k) ^ (2 ^ b) = 1 := by
      rw [← hψx, ← map_pow, hb, map_one]
    apply hk1
    have hd1 : orderOf (((ψ j)⁻¹ * c * ψ j * c⁻¹) ^ k) ∣ 1 := by
      have hc23 : Nat.Coprime (2 ^ b) 3 := Nat.Coprime.pow_left b (by norm_num)
      rw [← hc23.gcd_eq_one]
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hg2) (orderOf_dvd_of_pow_eq_one hk3)
    rw [Nat.dvd_one, orderOf_eq_one_iff] at hd1
    exact hd1
  ·
    have huO : ψ u ∈ omegaT := (hψO u).2 huN
    apply hno (ψ u) huO (by rw [← map_mul, huu, hψz])
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, hinv]

omit [Finite G] in
theorem ambientQuatDatum_map_omegaT {N : Subgroup G} [N.Normal] (e : ↥N ≃* ↥omegaT)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {K : Subgroup G} {z : G}
    (hd : Vtx.AmbientQuatDatum ⊤ K z) (hKN : K ≤ N) :
    Vtx.AmbientQuatDatum omegaT (K.map (phi e)) (phi e z) := by
  have hφ := phi_injective e hC
  obtain ⟨eK⟩ := hd.q8
  refine ⟨?_, ⟨(K.equivMapOfInjective (phi e) hφ).symm.trans eK⟩,
    Vtx.isUniqueInvolution_map (phi e) hφ hd.inv, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact phi_mem_omegaT_of_mem e (hKN hk)
  · intro c hc hcz
    obtain ⟨n, rfl⟩ := exists_of_mem_omegaT e hc
    have hn : (n : G) * z = z * n := hφ (by rw [map_mul, map_mul, hcz])
    rw [conjSub_map]
    rcases hd.twins n (Subgroup.mem_top _) hn with h1 | h1
    · left
      rw [h1]
    · right
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h1 x hx y hy]

end E4

theorem socleTransitive_o8p2 :
    SocleTransitive IsO8p2 := by
  intro G _ _ N _ _ _ hC hP Δ h hinvN
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hP
  have hθ : ∀ z : G, orderOf z = 2 → oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
    fun z hz => E4.oddCoreImg_centralizer_eq_bot (Vtx.autOddFree_of_lieModel_POmegaPlus hP) hC hz
  refine E4.conj_of_ident (E4.phi e) (E4.phi_injective e hC) (Kc := E4O8.K0) fun K hK => ?_
  obtain ⟨⟨z, hz⟩, -⟩ := h.hyp.omega1 K hK
  have hd := E4.ambientQuatDatum_of_mem h hθ hK hz
  have hKN := E4.le_of_mem e hC h hθ hK hz (hinvN K hK z hz)
  obtain ⟨g, hg, hgK⟩ := E4O8.ident_omega (E4.ambientQuatDatum_map_omegaT e hC hd hKN)
  obtain ⟨n, rfl⟩ := E4.exists_of_mem_omegaT e hg
  exact ⟨n, hgK⟩

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
