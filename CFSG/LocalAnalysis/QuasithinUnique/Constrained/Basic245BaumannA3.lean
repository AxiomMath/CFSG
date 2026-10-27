module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4BlockMore
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup CFSG.QuasithinUnique.DoubleA3
open scoped commutatorElement

namespace C56

variable {G : Type} [Group G]

theorem le_normalizer_of_commutator_eq {K J : Subgroup G} (h : ⁅K, J⁆ = K) :
    J ≤ normalizer (K : Set G) := by
  have key : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K := by
    intro j hj k hk
    have h1 : ⁅j, k⁆ ∈ ⁅K, J⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hj hk
    rw [h] at h1
    have e : j * k * j⁻¹ = ⁅j, k⁆ * k := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem h1 hk
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key j hj x, fun hx => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hx
  simpa [mul_assoc] using this

theorem a3_not_le_centralizer [Finite G] {K J : Subgroup G} (hK : IsShort2 K) (ha : IsAltType K 3)
    (hth : ⁅K, J⁆ = K) : ¬ J ≤ centralizer (blockU K : Set G) := by
  intro hJ
  have hA4 : IsA4Block K (blockU K) := IsA4Block.of_alt3 hK ha
  have hKU : K ≤ blockU K := by
    conv_lhs => rw [← hth]
    rw [Subgroup.commutator_le]
    intro k hk j hj
    have hkj : ⁅k, j⁆ ∈ K := by
      have := Subgroup.commutator_mem_commutator hk hj
      rwa [hth] at this
    refine hA4.mem_of_centralizes hkj fun u hu => ?_
    have hju : ∀ v ∈ blockU K, j * v = v * j := fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hJ hj) v hv).symm
    have hu' : k⁻¹ * u * k ∈ blockU K := by
      have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K (K.inv_mem hk)) u).mp hu
      simpa using this
    obtain ⟨u', hu'U, rfl⟩ : ∃ u' ∈ blockU K, u = k * u' * k⁻¹ := ⟨k⁻¹ * u * k, hu', by group⟩
    have h1 : Commute j⁻¹ (k * u' * k⁻¹) := Commute.inv_left (hju _ hu)
    have h2 : Commute j u' := hju _ hu'U
    calc ⁅k, j⁆ * (k * u' * k⁻¹) = k * j * k⁻¹ * (j⁻¹ * (k * u' * k⁻¹)) := by
          rw [commutatorElement_def]; group
      _ = k * j * k⁻¹ * ((k * u' * k⁻¹) * j⁻¹) := by rw [h1.eq]
      _ = k * (j * u') * k⁻¹ * j⁻¹ := by group
      _ = k * (u' * j) * k⁻¹ * j⁻¹ := by rw [h2.eq]
      _ = (k * u' * k⁻¹) * ⁅k, j⁆ := by rw [commutatorElement_def]; group
  have h1 := Subgroup.card_le_of_le hKU
  rw [hA4.card_L, hA4.card_U] at h1
  omega

theorem mem_of_isMaxElemAbelian_of_commute [Finite G] {R A : Subgroup G}
    (hA : IsMaxElemAbelian R A) {u : G} (huR : u ∈ R) (hc : ∀ a ∈ A, a * u = u * a)
    (hu2 : u ^ 2 = 1) : u ∈ A := by
  have hB := GammaExtra.isElemAbelian_sup_zpowers (le_refl A) hA.2.1 hc hu2
  have hBR : A ⊔ zpowers u ≤ R := sup_le hA.1 (zpowers_le.mpr huR)
  have heq : A = A ⊔ zpowers u := Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBR hB)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem omegaOneCenter_thompsonJ_le [Finite G] {R A : Subgroup G} (hA : IsMaxElemAbelian R A) :
    omegaOneCenterOf (thompsonJ R) ≤ A := by
  unfold omegaOneCenterOf omegaOneOf
  refine (Subgroup.closure_le A).mpr ?_
  rintro x ⟨hxZ, hx2⟩
  have hAJ : A ≤ thompsonJ R := GammaExtra.le_thompsonJ hA
  have hxZ' : x ∈ thompsonJ R ⊓ centralizer ((thompsonJ R : Subgroup G) : Set G) := hxZ
  refine mem_of_isMaxElemAbelian_of_commute hA (GammaExtra.thompsonJ_le_self R hxZ'.1) ?_ hx2
  intro a ha
  exact Subgroup.mem_centralizer_iff.mp hxZ'.2 a (hAJ ha)

theorem mem_centralizer_sup {A B : Subgroup G} {u : G} (hA : ∀ a ∈ A, a * u = u * a)
    (hB : ∀ b ∈ B, b * u = u * b) : u ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h1 : A ≤ centralizer ({u} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact (hA a ha).symm
  have h2 : B ≤ centralizer ({u} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]; exact (hB b hb).symm
  have h3 : A ⊔ B ≤ centralizer ({u} : Set G) := sup_le h1 h2
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    ((Subgroup.mem_centralizer_iff.mp (h3 hx)) u rfl).symm

theorem exists_isMaxElemAbelian_le_centralizer [Finite G] {R U : Subgroup G} (hR : IsPGroup 2 R)
    (hU4 : Nat.card U = 4) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hUR : U ≤ R) (hJU : thompsonJ R ≤ normalizer (U : Set G)) :
    ∃ A, IsMaxElemAbelian R A ∧ A ≤ centralizer (U : Set G) := by
  classical
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian R
  by_cases hc : A₀ ≤ centralizer (U : Set G)
  · exact ⟨A₀, hA₀, hc⟩
  have hA₀J : A₀ ≤ thompsonJ R := GammaExtra.le_thompsonJ hA₀
  have hA₀N : A₀ ≤ normalizer (U : Set G) := hA₀J.trans hJU
  have hBR : A₀ ⊔ U ≤ R := sup_le hA₀.1 hUR
  have hB2 : IsPGroup 2 ↥(A₀ ⊔ U) := hR.to_le hBR
  have hBN : A₀ ⊔ U ≤ normalizer (U : Set G) := sup_le hA₀N Subgroup.le_normalizer
  have hnt : ¬ A₀ ⊔ U ≤ centralizer (U : Set G) := fun h => hc (le_sup_left.trans h)
  obtain ⟨w, hwU, hw1, hrel, hCw, -, -⟩ := klein_structure hU4 hU2 le_sup_right hBN hB2 hnt
  have hwC : w ∈ U ⊓ centralizer ((A₀ ⊔ U : Subgroup G) : Set G) := by
    rw [hCw]; exact Subgroup.mem_zpowers w
  have hwcomm : ∀ a ∈ A₀, a * w = w * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hwC.2 a (Subgroup.mem_sup_left ha)
  have hwA : w ∈ A₀ :=
    mem_of_isMaxElemAbelian_of_commute hA₀ (hUR hwU) hwcomm (hU2 w hwU)
  have hA₀ab : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a :=
    GammaExtra.isMulCommutative_iff_forall.mp hA₀.2.1.1
  have hAU : A₀ ⊓ U = zpowers w := by
    apply le_antisymm
    · intro u hu
      rw [← hCw]
      refine ⟨hu.2, ?_⟩
      refine mem_centralizer_sup (A := A₀) (B := U) (fun a ha => hA₀ab a ha u hu.1) ?_
      intro v hv
      exact hUab v hv u hu.2
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨zpow_mem hwA k, zpow_mem hwU k⟩
  have hcardw : Nat.card (zpowers w) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hU2 w hwU) hw1]
  have hc1 := C5.card_sup_mul_card_inf_of_le_normalizer hA₀N
  rw [hAU, hcardw, hU4] at hc1
  have hc2 := DoubleA3.card_eq_card_mul_relIndex_of_le
    (inf_le_left : (A₀ ⊔ U) ⊓ centralizer (U : Set G) ≤ A₀ ⊔ U)
  rw [hrel] at hc2
  have hdec : ∀ x ∈ (A₀ ⊔ U) ⊓ centralizer (U : Set G), ∃ a ∈ A₀, ∃ u ∈ U, x = a * u ∧
      ∀ v ∈ U, a * v = v * a := by
    intro x hx
    obtain ⟨a, ha, u, hu, rfl⟩ := C5.mem_sup_of_le_normalizer hA₀N hx.1
    refine ⟨a, ha, u, hu, rfl, fun v hv => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 v hv
    have h3 : v * a * u = a * v * u := by
      calc v * a * u = v * (a * u) := by group
        _ = (a * u) * v := h1
        _ = a * (u * v) := by group
        _ = a * (v * u) := by rw [hUab u hu v hv]
        _ = a * v * u := by group
    exact (mul_right_cancel h3).symm
  have hea : IsElemAbelian 2 ((A₀ ⊔ U) ⊓ centralizer (U : Set G)) := by
    refine ⟨GammaExtra.isMulCommutative_iff_forall.mpr ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨a, ha, u, hu, rfl, hau⟩ := hdec x hx
      obtain ⟨a', ha', u', hu', rfl, hau'⟩ := hdec y hy
      calc a * u * (a' * u') = a * (u * a') * u' := by group
        _ = a * (a' * u) * u' := by rw [← hau' u hu]
        _ = (a * a') * (u * u') := by group
        _ = (a' * a) * (u' * u) := by rw [hA₀ab a ha a' ha', hUab u hu u' hu']
        _ = a' * (a * u') * u := by group
        _ = a' * (u' * a) * u := by rw [hau u' hu']
        _ = a' * u' * (a * u) := by group
    · intro x hx
      obtain ⟨a, ha, u, hu, rfl, hau⟩ := hdec x hx
      have ha2 : a ^ 2 = 1 := hA₀.2.1.2 a ha
      calc (a * u) ^ 2 = a * (u * a) * u := by rw [pow_two]; group
        _ = a * (a * u) * u := by rw [← hau u hu]
        _ = a ^ 2 * u ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [ha2, hU2 u hu, one_mul]
  refine ⟨(A₀ ⊔ U) ⊓ centralizer (U : Set G), ⟨inf_le_left.trans hBR, hea, ?_⟩, inf_le_right⟩
  intro B hBR' hB
  have := hA₀.2.2 B hBR' hB
  have hcA : Nat.card ↥((A₀ ⊔ U) ⊓ centralizer (U : Set G)) = Nat.card A₀ := by omega
  omega

theorem a3_blockU_le_baum [Finite G] {R K : Subgroup G} (hR : IsPGroup 2 R) (hK : IsShort2 K)
    (ha : IsAltType K 3) (hUR : blockU K ≤ R) (hth : ⁅K, thompsonJ R⁆ = K) :
    blockU K ≤ baum R ∧ ∃ z ∈ blockU K, z ≠ 1 ∧ z ∈ omegaOneCenterOf (thompsonJ R) := by
  classical
  have hA4 : IsA4Block K (blockU K) := IsA4Block.of_alt3 hK ha
  have hJK : thompsonJ R ≤ normalizer (K : Set G) := le_normalizer_of_commutator_eq hth
  have hJU : thompsonJ R ≤ normalizer (blockU K : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (hJK hg)
  have hJnc : ¬ thompsonJ R ≤ centralizer (blockU K : Set G) := a3_not_le_centralizer hK ha hth
  obtain ⟨A', hA'max, hA'c⟩ :=
    exists_isMaxElemAbelian_le_centralizer hR hA4.card_U hA4.sq_U hA4.comm_U hUR hJU
  have hEA' : omegaOneCenterOf (thompsonJ R) ≤ A' := omegaOneCenter_thompsonJ_le hA'max
  refine ⟨fun u hu => ⟨hUR hu, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp (hA'c (hEA' he)) u hu).symm
  · have hB₂ : IsPGroup 2 ↥(thompsonJ R ⊔ blockU K) :=
      hR.to_le (sup_le (GammaExtra.thompsonJ_le_self R) hUR)
    have hBN : thompsonJ R ⊔ blockU K ≤ normalizer (blockU K : Set G) :=
      sup_le hJU Subgroup.le_normalizer
    have hnt : ¬ thompsonJ R ⊔ blockU K ≤ centralizer (blockU K : Set G) := fun h =>
      hJnc (le_sup_left.trans h)
    obtain ⟨z, hzU, hz1, -, hCz, -, -⟩ :=
      klein_structure hA4.card_U hA4.sq_U le_sup_right hBN hB₂ hnt
    have hzC : z ∈ blockU K ⊓ centralizer ((thompsonJ R ⊔ blockU K : Subgroup G) : Set G) := by
      rw [hCz]; exact Subgroup.mem_zpowers z
    have hzJ : ∀ j ∈ thompsonJ R, j * z = z * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp hzC.2 j (Subgroup.mem_sup_left hj)
    obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian R
    have hzA₀ : z ∈ A₀ :=
      mem_of_isMaxElemAbelian_of_commute hA₀ (hUR hzU)
        (fun a ha => hzJ a (GammaExtra.le_thompsonJ hA₀ ha)) (hA4.sq_U z hzU)
    have hzJ' : z ∈ thompsonJ R := GammaExtra.le_thompsonJ hA₀ hzA₀
    refine ⟨z, hzU, hz1, Subgroup.subset_closure ⟨?_, hA4.sq_U z hzU⟩⟩
    show z ∈ thompsonJ R ⊓ centralizer ((thompsonJ R : Subgroup G) : Set G)
    exact ⟨hzJ', Subgroup.mem_centralizer_iff.mpr fun j hj => hzJ j hj⟩

theorem a3_baum_le_normalizer [Finite G] {R K : Subgroup G} (hR : IsPGroup 2 R) (hK : IsShort2 K)
    (ha : IsAltType K 3) (hUR : blockU K ≤ R) (hth : ⁅K, thompsonJ R⁆ = K)
    (hperm : ∀ s ∈ baum R, conjSubgroup K s = K ∨
      ∀ a ∈ K, ∀ b ∈ conjSubgroup K s, a * b = b * a) :
    baum R ≤ normalizer (K : Set G) := by
  obtain ⟨-, z, hzU, hz1, hzE⟩ := a3_blockU_le_baum hR hK ha hUR hth
  have hA4 : IsA4Block K (blockU K) := IsA4Block.of_alt3 hK ha
  intro s hs
  rcases hperm s hs with h | h
  · exact conjSubgroup_eq_iff_mem_normalizer.mp h
  · exfalso
    have hzs : z * s = s * z := Subgroup.mem_centralizer_iff.mp hs.2 z hzE
    have hzK : z ∈ K := hA4.le hzU
    have hzKs : z ∈ conjSubgroup K s := by
      rw [mem_conjSubgroup_iff]
      have : s * z * s⁻¹ = z := by rw [← hzs]; group
      rw [this]; exact hzK
    apply hz1
    exact hA4.center_L z hzK fun l hl => (h l hl z hzKs).symm

theorem a3_isSylowTwoOf_sup [Finite G] {L B : Subgroup G} (hLs : IsShort2 L) (ha : IsAltType L 3)
    (hB2 : IsPGroup 2 B) (hUB : blockU L ≤ B) (hBN : B ≤ normalizer (L : Set G)) :
    IsSylowTwoOf B (L ⊔ B) := by
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hLs ha
  have hLB : L ⊓ B = blockU L := by
    refine le_antisymm ?_ (le_inf hUL hUB)
    have h2 : IsPGroup 2 ↥(L ⊓ B) := hB2.to_le inf_le_right
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdvd : Nat.card ↥(L ⊓ B) ∣ Nat.card ↥L := Subgroup.card_dvd_of_le inf_le_left
    rw [hn, hA4.card_L] at hdvd
    have hn2 : n ≤ 2 := by
      by_contra hcon
      have h8 : 2 ^ 3 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
      have := h8.trans hdvd
      omega
    have hcard : Nat.card ↥(L ⊓ B) ≤ Nat.card ↥(blockU L) := by
      rw [hn, hA4.card_U]
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
        _ = 4 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hUL hUB) hcard).ge
  have hcardX : Nat.card ↥(L ⊔ B) = 3 * Nat.card ↥B := by
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hBN
    rw [sup_comm, inf_comm, hLB, hA4.card_U, hA4.card_L] at h1
    omega
  have hrel : B.relIndex (L ⊔ B) = 3 := by
    have h1 := C5.card_eq_card_mul_relIndex (le_sup_right : B ≤ L ⊔ B)
    rw [hcardX] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm (Nat.card ↥B) 3]; exact h1)).symm
  refine ⟨le_sup_right, hB2, ?_⟩
  show ¬ 2 ∣ B.relIndex (L ⊔ B)
  rw [hrel]
  omega

theorem baumann_A3_single [Finite G] {R H L : Subgroup G} (hmin : IsMinimalParabolic R H)
    (hblk : IsChi0Block H L) (ha : IsAltType L 3) (hth : ⁅L, thompsonJ R⁆ = L)
    (hHLR : H = L ⊔ R) (hRN : R ≤ normalizer (L : Set G)) :
    blockU L ≤ baum R ∧ baum R ≤ normalizer (L : Set G) ∧
      IsSylowTwoOf (baum R) (L ⊔ baum R) := by
  have hLs : IsShort2 L := hblk.1.1
  have hLH : L ≤ H := hblk.1.2.1
  have hHN : H ≤ normalizer (L : Set G) := by
    rw [hHLR]; exact sup_le Subgroup.le_normalizer hRN
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hUR : blockU L ≤ R :=
    hmin.1.le_of_normalizes (hUL.trans hLH) (fun g hg => C1.mem_normalizer_blockU (hHN hg))
      (C1.isPGroup_blockU hLs)
  have hR2 : IsPGroup 2 R := hmin.1.isPGroup
  obtain ⟨hUB, -⟩ := a3_blockU_le_baum hR2 hLs ha hUR hth
  have hBR : baum R ≤ R := inf_le_left
  have hBN : baum R ≤ normalizer (L : Set G) := hBR.trans hRN
  exact ⟨hUB, hBN, a3_isSylowTwoOf_sup hLs ha (hR2.to_le hBR) hUB hBN⟩

end C56

end CFSG.QuasithinUnique
