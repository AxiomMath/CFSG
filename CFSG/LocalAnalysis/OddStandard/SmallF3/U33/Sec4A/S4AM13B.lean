module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section M13B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m13_card_B (h : Ctx0 t L S x₁ x₂ lam rho) : Nat.card (baseGrp x₁ x₂) = 16 :=
  (h.wreath.baseGrp_eq).2.2

theorem m13_relIndex_RF (h : L41GPh8 t L S x₁ x₂ lam rho) :
    (l41R t x₁ x₂ rho).relIndex (l41F t x₁ x₂ rho) = 2 := by
  have hRF : l41R t x₁ x₂ rho ≤ l41F t x₁ x₂ rho := le_sup_left
  have h1 := Subgroup.relIndex_mul_card (H := l41R t x₁ x₂ rho) (K := l41F t x₁ x₂ rho)
  rw [inf_eq_left.mpr hRF, h.rfacts.card_R, m13_card_F h] at h1
  omega

theorem m13_abel_le (h : L41GPh10 t L S x₁ x₂ lam rho) {A : Subgroup G}
    (hAF : A ≤ l41F t x₁ x₂ rho) (hAc : IsMulCommutative ↥A)
    (hAR : ¬ A ≤ l41R t x₁ x₂ rho) : Nat.card A ≤ 32 := by
  obtain ⟨a, haA, haR⟩ := SetLike.not_le_iff_exists.mp hAR
  rcases m13_mem_F h.toL41GPh8 (hAF haA) with h1 | ⟨k, hk, hak⟩
  · exact absurd h1 haR
  · have hle : A ⊓ l41R t x₁ x₂ rho ≤ baseGrp x₁ x₂ := by
      intro r hr
      obtain ⟨hrA, hrR⟩ := Subgroup.mem_inf.mp hr
      have hcomm : r * a = a * r :=
        congrArg Subtype.val (mul_comm' (⟨r, hrA⟩ : ↥A) ⟨a, haA⟩)
      rw [← m13_cent_tk h hk]
      refine Subgroup.mem_inf.mpr ⟨hrR, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hak]
      exact hcomm
    have hcardB := Subgroup.card_le_of_le hle
    rw [m13_card_B h.toCtx0] at hcardB
    have h1 := Subgroup.relIndex_mul_card (H := l41R t x₁ x₂ rho) (K := A)
    have h2 : (l41R t x₁ x₂ rho).relIndex A ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := l41R t x₁ x₂ rho) hAF
        (by rw [m13_relIndex_RF h.toL41GPh8]; norm_num)
      rwa [m13_relIndex_RF h.toL41GPh8] at this
    rw [inf_comm] at h1
    calc Nat.card A = (l41R t x₁ x₂ rho).relIndex A * Nat.card ↥(A ⊓ l41R t x₁ x₂ rho) :=
          h1.symm
      _ ≤ 2 * 16 := Nat.mul_le_mul h2 hcardB

theorem m13_J0 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    CFSG.ambientMaxCardThompson (l41F t x₁ x₂ rho) = l41R t x₁ x₂ rho := by
  have hRF : l41R t x₁ x₂ rho ≤ l41F t x₁ x₂ rho := le_sup_left
  have hmax : ∀ B : Subgroup G, B ≤ l41F t x₁ x₂ rho → IsMulCommutative ↥B →
      Nat.card B ≤ 64 := by
    intro B hBF hBc
    by_cases hBR : B ≤ l41R t x₁ x₂ rho
    · have := Subgroup.card_le_of_le hBR
      rw [h.rfacts.card_R] at this
      norm_num at this
      exact this
    · have := m13_abel_le h hBF hBc hBR
      omega
  have hmem : l41R t x₁ x₂ rho ∈ CFSG.ambientMaxCardAbelianFamily (l41F t x₁ x₂ rho) :=
    ⟨hRF, h.rab, fun B hBF hBc => by
      rw [h.rfacts.card_R]
      have := hmax B hBF hBc
      omega⟩
  have hfam : CFSG.ambientMaxCardAbelianFamily (l41F t x₁ x₂ rho) = {l41R t x₁ x₂ rho} := by
    ext A
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hA
      have h1 : Nat.card (l41R t x₁ x₂ rho) ≤ Nat.card A := hA.2.2 _ hRF h.rab
      by_cases hAR : A ≤ l41R t x₁ x₂ rho
      · exact Subgroup.eq_of_le_of_card_ge hAR h1
      · exfalso
        have := m13_abel_le h hA.1 hA.2.1 hAR
        rw [h.rfacts.card_R] at h1
        omega
    · rintro rfl
      exact hmem
  rw [CFSG.ambientMaxCardThompson, hfam, sSup_singleton]

theorem m13_normal_R (h : L41GPh10 t L S x₁ x₂ lam rho) :
    NormalIn (l41R t x₁ x₂ rho) (l41M t x₁ x₂ rho) := by
  refine ⟨(le_sup_left : l41R t x₁ x₂ rho ≤ l41F t x₁ x₂ rho).trans Subgroup.le_normalizer,
    fun g hg k hk => ?_⟩
  have h1 := CFSG.normalizer_le_normalizer_ambientMaxCardThompson (l41F t x₁ x₂ rho) hg
  rw [m13_J0 h] at h1
  exact (Subgroup.mem_normalizer_iff.mp h1 k).mp hk

theorem m13_Y_le_R (t x₁ x₂ rho : G) : l41Y t x₁ x₂ rho ≤ l41R t x₁ x₂ rho :=
  (Subgroup.closure_le _).mpr fun _ hg => hg.1

theorem m13_normal_Y (h : L41GPh10 t L S x₁ x₂ lam rho) :
    NormalIn (l41Y t x₁ x₂ rho) (l41M t x₁ x₂ rho) := by
  have hNR := m13_normal_R h
  refine ⟨(m13_Y_le_R t x₁ x₂ rho).trans hNR.1, fun g hg => ?_⟩
  have hle : l41Y t x₁ x₂ rho ≤ (l41Y t x₁ x₂ rho).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    show g * u * g⁻¹ ∈ l41Y t x₁ x₂ rho
    refine Subgroup.subset_closure ⟨hNR.2 g hg u hu.1, ?_⟩
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu.2]; group
  intro y hy
  exact hle hy

theorem m13_base_comm_F (h : L41GPh10 t L S x₁ x₂ lam rho) {b f : G} (hb : b ∈ baseGrp x₁ x₂)
    (hf : f ∈ l41F t x₁ x₂ rho) : b * f = f * b := by
  have hbR := n4_base_le_R h.toL41GPh3 hb
  rcases m13_mem_F h.toL41GPh8 hf with h1 | ⟨k, hk, rfl⟩
  · exact m13_comm_R h hbR h1
  · have htb := m13_t_comm_base h.toL41GPh5 hb
    have hbk := m13_comm_R h hbR hk
    calc b * (t * k) = (b * t) * k := (mul_assoc _ _ _).symm
      _ = (t * b) * k := by rw [htb]
      _ = t * (b * k) := mul_assoc _ _ _
      _ = t * (k * b) := by rw [hbk]
      _ = t * k * b := (mul_assoc _ _ _).symm

theorem m13_cent_F (h : L41GPh10 t L S x₁ x₂ lam rho) :
    centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) = baseGrp x₁ x₂ := by
  have hP : twoCore t = zpowers t := h.p2
  have hRF : l41R t x₁ x₂ rho ≤ l41F t x₁ x₂ rho := le_sup_left
  apply le_antisymm
  · intro g hg
    have hA : ctxE t x₁ x₂ ≤ l41F t x₁ x₂ rho := by
      rw [pt_ctxE_eq_sup]
      refine sup_le ?_ (h.rfacts.fourGrp_le.trans hRF)
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hgW : g ∈ ctxW t x₁ x₂ := by
      rw [← h.basic.cent_A]
      exact Subgroup.centralizer_le (fun a ha => hA ha) hg
    obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_base h.toCtx0)).mp hgW
    have hbC : b ∈ centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun f hf => (m13_base_comm_F h hb hf).symm
    have hpC : p ∈ centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hbC)
      rwa [mul_inv_cancel_right] at this
    rw [hP] at hp
    rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
    · rw [h1, one_mul]
      exact hb
    · exfalso
      rw [h1] at hpC
      have hRB : l41R t x₁ x₂ rho ≤ baseGrp x₁ x₂ := by
        intro r hr
        rw [← h.rfacts.cent_t]
        refine Subgroup.mem_inf.mpr ⟨hr, ?_⟩
        rw [mem_invCent_iff]
        exact Subgroup.mem_centralizer_iff.mp hpC r (hRF hr)
      have := Subgroup.card_le_of_le hRB
      rw [h.rfacts.card_R, m13_card_B h.toCtx0] at this
      norm_num at this
  · intro b hb
    exact Subgroup.mem_centralizer_iff.mpr fun f hf => (m13_base_comm_F h hb hf).symm

theorem eq_one_of_mem_odd_of_mem_two_group {M : Subgroup G} {K : Subgroup ↥M}
    (hKodd : Odd (Nat.card K)) {c : ↥M} (hcK : c ∈ K) {Q : Subgroup G} {k : ℕ}
    (hQ : Nat.card Q = 2 ^ k) (hcQ : (c : G) ∈ Q) : c = 1 := by
  have h1 : orderOf c ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨c, hcK⟩ : ↥K)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf c ∣ 2 ^ k := by
    have := orderOf_dvd_natCard (⟨(c : G), hcQ⟩ : ↥Q)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hQ] at this
    exact this
  have hcop : Nat.Coprime (Nat.card K) (2 ^ k) :=
    Nat.Coprime.pow_right k (Odd.coprime_two_right hKodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem m13_oddCore (h : L41GPh10 t L S x₁ x₂ lam rho) :
    CFSG.oddCore ↥(l41M t x₁ x₂ rho) = ⊥ := by
  rw [eq_bot_iff, CFSG.oddCore]
  refine sSup_le fun K hK => ?_
  obtain ⟨hKn, hKodd⟩ := hK
  intro n hn
  rw [Subgroup.mem_bot]
  have hcomm : ∀ f ∈ l41F t x₁ x₂ rho, f * (n : G) = (n : G) * f := by
    intro f hf
    have hfM : f ∈ l41M t x₁ x₂ rho := Subgroup.le_normalizer hf
    set f' : ↥(l41M t x₁ x₂ rho) := ⟨f, hfM⟩ with hf'
    have hcK : n * f' * n⁻¹ * f'⁻¹ ∈ K := by
      have h1 := hKn.conj_mem n⁻¹ (K.inv_mem hn) f'
      have e : n * f' * n⁻¹ * f'⁻¹ = n * (f' * n⁻¹ * f'⁻¹) := by group
      rw [e]
      exact K.mul_mem hn h1
    have hcF : ((n * f' * n⁻¹ * f'⁻¹ : ↥(l41M t x₁ x₂ rho)) : G) ∈ l41F t x₁ x₂ rho := by
      have h1 : (n : G) * f * (n : G)⁻¹ ∈ l41F t x₁ x₂ rho :=
        (Subgroup.mem_normalizer_iff.mp n.2 f).mp hf
      have e : ((n * f' * n⁻¹ * f'⁻¹ : ↥(l41M t x₁ x₂ rho)) : G) =
          ((n : G) * f * (n : G)⁻¹) * f⁻¹ := rfl
      rw [e]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hf)
    have h1 := eq_one_of_mem_odd_of_mem_two_group hKodd hcK (m13_card_F h.toL41GPh8) hcF
    have h2 := congrArg Subtype.val h1
    have e : ((n * f' * n⁻¹ * f'⁻¹ : ↥(l41M t x₁ x₂ rho)) : G) =
        (n : G) * f * (n : G)⁻¹ * f⁻¹ := rfl
    rw [e] at h2
    change (n : G) * f * (n : G)⁻¹ * f⁻¹ = 1 at h2
    have h3 : (n : G) * f = f * (n : G) := by
      calc (n : G) * f = ((n : G) * f * (n : G)⁻¹ * f⁻¹) * (f * (n : G)) := by group
        _ = f * (n : G) := by rw [h2, one_mul]
    exact h3.symm
  have hnC : (n : G) ∈ centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr hcomm
  rw [m13_cent_F h] at hnC
  have hB : Nat.card (baseGrp x₁ x₂) = 2 ^ 4 := by
    rw [m13_card_B h.toCtx0]
    norm_num
  exact eq_one_of_mem_odd_of_mem_two_group hKodd hn hB hnC

end M13B

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
