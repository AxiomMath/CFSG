module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Tail

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

@[expose] def NaturalConcl {G : Type} [Group G] (R H L : Subgroup G) : Prop :=
  ∃ (q : ℕ) (W : Subgroup G), 2 ≤ q ∧ W ≤ blockU L ∧
    (baum R ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex (baum R) = q ∧
    W.relIndex (blockU L) = q ∧
    (∀ y ∈ baum R, y ∉ baum R ⊓ Subgroup.centralizer (blockU L : Set G) →
      ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u)) ∧
    ⁅blockU L, baum R⁆ = W ∧
    (blockU L ⊓ Subgroup.centralizer (L : Set G)).relIndex (blockU L) = q ^ 2 ∧
    (∀ y ∈ Subgroup.normalizer (baum R : Set G),
      ¬ conjSubgroup (blockU L) y ≤ baum R ⊓ Subgroup.centralizer (blockU L : Set G) →
      ¬ conjSubgroup (blockU L) y⁻¹ ≤ baum R ⊓ Subgroup.centralizer (blockU L : Set G) →
      ∃ k ∈ L, L ≤ conjSubgroup (blockU L) y ⊔ conjSubgroup (conjSubgroup (blockU L) y) k) ∧
    (∀ r ∈ R, (∀ b ∈ baum R, r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 H) → r ∈ baum R ⊔ pCoreOf 2 H)

theorem naturalModuleStructure_iff : NaturalModuleStructure ↔
    ∀ (G : Type) [Group G] [Finite G] (R H L : Subgroup G),
      IsMinimalParabolic R H → CharTwo H → IsChi0Block H L →
      ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) →
      ⁅L, thompsonJ R⁆ = L → H = L ⊔ R → R ≤ Subgroup.normalizer (L : Set G) →
        NaturalConcl R H L :=
  Iff.rfl

namespace C56

variable {G : Type} [Group G] [Finite G]

theorem baum_inf_centralizer_eq {L B : Subgroup G} (hL : IsShort2 L) (hB2 : IsPGroup 2 B)
    (hBN : B ≤ normalizer (L : Set G)) (hsyl : IsSylowTwoOf B (L ⊔ B)) :
    B ⊓ centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ B) := by
  have hLX : L ≤ L ⊔ B := le_sup_left
  have hBX : B ≤ L ⊔ B := le_sup_right
  have hXN : L ⊔ B ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hXpow : ∀ g ∈ L ⊔ B, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun _ hg =>
    C1.exists_pow_mem_of_mem_sup hB2 hBN hg
  have hC111X : (L ⊔ B) ⊓ centralizer (blockU L : Set G) = pCoreOf 2 (L ⊔ B) :=
    C1.inf_centralizer_blockU_eq hL hLX hXN hXpow
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · have : g ∈ (L ⊔ B) ⊓ centralizer (blockU L : Set G) := ⟨hBX hg.1, hg.2⟩
    rwa [hC111X] at this
  · have h1 : g ∈ (L ⊔ B) ⊓ centralizer (blockU L : Set G) := by rw [hC111X]; exact hg
    exact ⟨hsyl.pCoreOf_le hg, h1.2⟩

omit [Finite G] in
theorem le_of_le_sup_isPGroup {L Λ Q : Subgroup G} (hL : IsShort2 L) (hQ2 : IsPGroup 2 Q)
    (hQΛ : Q ≤ normalizer (Λ : Set G)) (hLΛQ : L ≤ Λ ⊔ Q) : L ≤ Λ := by
  let N' : Subgroup L := Λ.subgroupOf L
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Λ := hn
    have hgΛQ : (g : G) ∈ Q ⊔ Λ := by rw [sup_comm]; exact hLΛQ g.2
    obtain ⟨q, hq, l', hl', hg⟩ := C5.mem_sup_of_le_normalizer hQΛ hgΛQ
    show (g : G) * n * (g : G)⁻¹ ∈ Λ
    rw [hg]
    have h1 : l' * (n : G) * l'⁻¹ ∈ Λ := mul_mem (mul_mem hl' hn') (inv_mem hl')
    have h2 : q * (l' * (n : G) * l'⁻¹) * q⁻¹ ∈ Λ :=
      (Subgroup.mem_normalizer_iff.mp (hQΛ hq) _).mp h1
    have e : q * l' * (n : G) * (q * l')⁻¹ = q * (l' * (n : G) * l'⁻¹) * q⁻¹ := by group
    rw [e]
    exact h2
  have hq : IsPGroup 2 (L ⧸ N') := by
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := C1.exists_pow_mem_of_mem_sup hQ2 hQΛ (show (l : G) ∈ Λ ⊔ Q from hLΛQ l.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have htop := hL.1 N' hq
  intro l hl
  have : (⟨l, hl⟩ : L) ∈ N' := by rw [htop]; trivial
  exact this

theorem natural_A3 {R H L : Subgroup G}
    (hmin : IsMinimalParabolic R H) (hblk : IsChi0Block H L)
    (h3 : IsAltType L 3) (hth : ⁅L, thompsonJ R⁆ = L) (hHLR : H = L ⊔ R)
    (hRN : R ≤ normalizer (L : Set G)) : NaturalConcl R H L := by
  have hLsh : IsShort2 L := hblk.1.1
  obtain ⟨hBN, hBsyl⟩ := baumann_single hmin hblk (Or.inr h3) hth hHLR hRN
  obtain ⟨-, hU4, hU2, hUab, -, -, c, hcL, hc3, hcN, hcfix, hLc⟩ := hLsh.alt3_structure h3
  have hQU : blockQ L = blockU L := (hLsh.alt3_structure h3).1
  have hL12 : Nat.card L = 12 := (hLsh.alt3_structure h3).2.2.2.2.1
  set B := baum R with hBdef
  set U := blockU L with hUdef
  have hBR : B ≤ R := inf_le_left
  have hR2 : IsPGroup 2 R := hmin.1.isPGroup
  have hB2 : IsPGroup 2 B := hR2.to_le hBR
  have hBU : B ≤ normalizer (U : Set G) := fun g hg => C1.mem_normalizer_blockU (hBN hg)
  set X := L ⊔ B with hXdef
  have hLX : L ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXN : X ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hXU : X ≤ normalizer (U : Set G) := sup_le (C1.le_normalizer_blockU L) hBU
  have hQX : B ⊓ centralizer (U : Set G) = pCoreOf 2 X := baum_inf_centralizer_eq hLsh hB2 hBN hBsyl
  have hUL : U ≤ L := (C1.blockU_le_blockQ hLsh).trans (C1.blockQ_le L)
  have hUB : U ≤ B := hBsyl.le_of_normalizes (hUL.trans hLX) hXU (C1.isPGroup_blockU hLsh)
  have hXQ : X ≤ normalizer ((pCoreOf 2 X : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hnt : ¬ B ≤ centralizer (U : Set G) := by
    intro hBc
    have hBQ : B = pCoreOf 2 X := by rw [← hQX]; exact (inf_eq_left.mpr hBc).symm
    have hBXn : X ≤ normalizer (B : Set G) := by rw [hBQ]; exact hXQ
    have hJB : thompsonJ R ≤ B := C5.thompsonJ_le_baum' R
    have hcomm : ⁅L, thompsonJ R⁆ ≤ B := by
      rw [Subgroup.commutator_le]
      intro l hl j hj
      have h1 : l * j * l⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hBXn (hLX hl)) j).mp (hJB hj)
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem (hJB hj))
    have hLB : L ≤ B := hth ▸ hcomm
    have hLp : IsPGroup 2 L := hB2.to_le hLB
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hLp.exists_card_eq
    have h3d : 3 ∣ 2 ^ k := by rw [← hk, hL12]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    omega
  obtain ⟨z, hzU, hz1, -, hR1⟩ := DoubleA3.rank1_of_klein hU4 hU2 hUab hUB hBU hB2 hnt
  set Q := B ⊓ centralizer (U : Set G) with hQdef
  have hKQ : L ≤ normalizer (Q : Set G) := by rw [hQX]; exact hLX.trans hXQ
  have hQ2 : IsPGroup 2 Q := hB2.to_le inf_le_left
  have hUQ : U ≤ Q := hR1.U_le_Q
  have hgen : ∀ y ∈ normalizer (B : Set G), ¬ conjSubgroup U y ≤ Q → ¬ conjSubgroup U y⁻¹ ≤ Q →
      ∃ k ∈ L, L ≤ conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) k := by
    intro y hy hy1 _
    refine ⟨c, hcL, ?_⟩
    obtain ⟨y₁, hy₁U, hy₁Q⟩ := IsConcreteLE.not_le_iff_exists.mp hy1
    have hy₁B : y₁ ∈ B := hR1.conj_le_B hy hy₁U
    have hs : y₁ * y₁ ∈ Q := mul_self_mem_of_relIndex_two hR1.idx_Q hy₁B hy₁Q
    have hy₁L : y₁ * c * y₁⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hBN hy₁B) c).mp hcL
    have hcc : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
    have hzc : zpowers c ≤ normalizer (U : Set G) := Subgroup.zpowers_le.mpr hcN
    have hmem : y₁ * c * y₁⁻¹ ∈ zpowers c ⊔ U := by rw [sup_comm, ← hLc]; exact hy₁L
    obtain ⟨cm, hcm, u, hu, hdec⟩ := C5.mem_sup_of_le_normalizer hzc hmem
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcm
    have hcpow : c ^ m = 1 ∨ c ^ m = c ∨ c ^ m = c⁻¹ := by
      have h := zpow_mod_orderOf c m
      rw [hc3] at h
      have h' : (m % (3 : ℤ)) = 0 ∨ m % (3 : ℤ) = 1 ∨ m % (3 : ℤ) = 2 := by omega
      rcases h' with h0 | h0 | h0
      · left; rw [← h]; push_cast at h0 ⊢; rw [h0]; simp
      · right; left; rw [← h]; push_cast at h0 ⊢; rw [h0]; simp
      · right; right; rw [← h]; push_cast at h0 ⊢; rw [h0]
        have : c ^ (2 : ℤ) * c = 1 := by
          rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_succ]; exact hcc
        exact eq_inv_of_mul_eq_one_left this
    have hu2 : u ^ 2 = 1 := hU2 u hu
    rcases hcpow with h1 | h1 | h1
    ·
      exfalso
      rw [h1, one_mul] at hdec
      have h3' : (y₁ * c * y₁⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hcc]; group
      rw [hdec] at h3'
      have : u = 1 := by
        have e : u = u ^ 3 * (u ^ 2)⁻¹ := by group
        rw [e, h3', hu2]; group
      rw [this] at hdec
      have : c = 1 := by
        have e : c = y₁⁻¹ * (y₁ * c * y₁⁻¹) * y₁ := by group
        rw [e, hdec]; group
      rw [this, orderOf_one] at hc3
      omega
    ·
      exfalso
      rw [h1] at hdec
      have hzW : z ∈ zpowers z := Subgroup.mem_zpowers z
      have hzy : z * y₁ = y₁ * z := (hR1.cent_y y₁ hy₁B hy₁Q z hzU).mp hzW
      have hv : c * z * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hcN z).mp hzU
      have hy₁z : y₁ * z * y₁⁻¹ = z := by
        have : y₁ * z = z * y₁ := hzy.symm
        rw [this]; group
      have hconj : y₁ * (c * z * c⁻¹) * y₁⁻¹ = c * z * c⁻¹ := by
        have e : y₁ * (c * z * c⁻¹) * y₁⁻¹ =
            (y₁ * c * y₁⁻¹) * (y₁ * z * y₁⁻¹) * (y₁ * c * y₁⁻¹)⁻¹ := by group
        rw [e, hdec, hy₁z]
        have hcu : u * z = z * u := hUab u hu z hzU
        calc c * u * z * (c * u)⁻¹ = c * (u * z) * u⁻¹ * c⁻¹ := by group
          _ = c * (z * u) * u⁻¹ * c⁻¹ := by rw [hcu]
          _ = c * z * c⁻¹ := by group
      have hvc : (c * z * c⁻¹) * y₁ = y₁ * (c * z * c⁻¹) := by
        have h' : y₁ * (c * z * c⁻¹) = (c * z * c⁻¹) * y₁ := by
          calc y₁ * (c * z * c⁻¹) = y₁ * (c * z * c⁻¹) * y₁⁻¹ * y₁ := by group
            _ = (c * z * c⁻¹) * y₁ := by rw [hconj]
        exact h'.symm
      have hvW : c * z * c⁻¹ ∈ zpowers z := (hR1.cent_y y₁ hy₁B hy₁Q _ hv).mpr hvc
      rcases (DoubleA3.mem_zpowers_iff_of_sq_eq_one (hU2 z hzU)).mp hvW with h2 | h2
      · apply hz1
        have : z = c⁻¹ * (c * z * c⁻¹) * c := by group
        rw [this, h2]; group
      · exact hcfix z hzU hz1 h2
    ·
      rw [h1] at hdec
      set Ut := conjSubgroup U y with hUt
      set Λ := Ut ⊔ conjSubgroup Ut c with hΛ
      have hy₁Λ : y₁ ∈ Λ := Subgroup.mem_sup_left hy₁U
      have hy₁cΛ : c⁻¹ * y₁ * c ∈ Λ := by
        refine Subgroup.mem_sup_right ?_
        rw [mem_conjSubgroup_iff]
        have : c * (c⁻¹ * y₁ * c) * c⁻¹ = y₁ := by group
        rw [this]; exact hy₁U
      have hcQ : c ∈ normalizer (Q : Set G) := hKQ hcL
      have hsc : c * (y₁ * y₁) * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hcQ _).mp hs
      have hinv : y₁ * c⁻¹ * y₁⁻¹ = u⁻¹ * c := by
        have : (y₁ * c * y₁⁻¹)⁻¹ = y₁ * c⁻¹ * y₁⁻¹ := by group
        rw [← this, hdec]; group
      have hc2 : c * c ∈ Λ ⊔ Q := by
        have e : y₁ * (c⁻¹ * y₁ * c) = (u⁻¹ * (c * (y₁ * y₁) * c⁻¹)) * (c * c) := by
          calc y₁ * (c⁻¹ * y₁ * c) = (y₁ * c⁻¹ * y₁⁻¹) * (y₁ * y₁) * c := by group
            _ = (u⁻¹ * c) * (y₁ * y₁) * c := by rw [hinv]
            _ = (u⁻¹ * (c * (y₁ * y₁) * c⁻¹)) * (c * c) := by group
        have : c * c = (u⁻¹ * (c * (y₁ * y₁) * c⁻¹))⁻¹ * (y₁ * (c⁻¹ * y₁ * c)) := by
          rw [e]; group
        rw [this]
        exact mul_mem (inv_mem (mul_mem (Subgroup.mem_sup_right (hUQ (inv_mem hu)))
          (Subgroup.mem_sup_right hsc))) (mul_mem (Subgroup.mem_sup_left hy₁Λ)
          (Subgroup.mem_sup_left hy₁cΛ))
      have hc4 : (c * c) * (c * c) = c := by
        have h3 : c * c * c = 1 := by rw [← hcc, pow_succ, pow_two]
        calc (c * c) * (c * c) = (c * c * c) * c := by group
          _ = c := by rw [h3, one_mul]
      have hcmem : c ∈ Λ ⊔ Q := by rw [← hc4]; exact mul_mem hc2 hc2
      have hLΛQ : L ≤ Λ ⊔ Q :=
        hLc.le.trans (sup_le (hUQ.trans le_sup_right) (Subgroup.zpowers_le.mpr hcmem))
      have hQUt : Q ≤ normalizer (Ut : Set G) := fun g hg =>
        hR1.B_le_normU_conj hy (hR1.Q_le_B hg)
      have hQΛ : Q ≤ normalizer (Λ : Set G) := by
        intro g hg
        have h2 : g ∈ normalizer ((conjSubgroup Ut c : Subgroup G) : Set G) := by
          have := C5.conjSubgroup_mono hQUt c
          rw [C5.conjSubgroup_eq_self hcQ, C5.conjSubgroup_normalizer] at this
          exact this hg
        exact C1.mem_normalizer_sup (hQUt hg) h2
      exact le_of_le_sup_isPGroup hLsh hQ2 hQΛ hLΛQ
  have hHN : H ≤ normalizer (L : Set G) := hHLR ▸ sup_le Subgroup.le_normalizer hRN
  have hHpow : ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun g hg =>
    C1.exists_pow_mem_of_mem_sup hR2 hRN (hHLR ▸ hg)
  have hC111 : H ⊓ centralizer (U : Set G) = pCoreOf 2 H :=
    C1.inf_centralizer_blockU_eq hLsh (hHLR ▸ le_sup_left) hHN hHpow
  have hPR : pCoreOf 2 H ≤ R := hmin.1.pCoreOf_le
  have hRC : R ⊓ centralizer (U : Set G) = pCoreOf 2 H := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨hPR hg, ?_⟩)
    · have : g ∈ H ⊓ centralizer (U : Set G) := ⟨hmin.1.le hg.1, hg.2⟩
      rwa [hC111] at this
    · have : g ∈ H ⊓ centralizer (U : Set G) := by rw [hC111]; exact hg
      exact this.2
  have hSC : ∀ r ∈ R, (∀ b ∈ B, r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 H) → r ∈ B ⊔ pCoreOf 2 H := by
    intro r hr _
    have hRNU : R ≤ normalizer (U : Set G) := fun g hg => C1.mem_normalizer_blockU (hRN hg)
    have hRnt : ¬ R ≤ centralizer (U : Set G) := fun h => hnt (hBR.trans h)
    obtain ⟨-, -, -, hRidx, -⟩ :=
      DoubleA3.klein_structure hU4 hU2 (hUB.trans hBR) hRNU hR2 hRnt
    rw [hRC] at hRidx
    obtain ⟨b₀, hb₀B, hb₀c⟩ : ∃ b ∈ B, b ∉ centralizer (U : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hnt fun b hb => hcon b hb
    have hb₀P : b₀ ∉ pCoreOf 2 H := fun h => hb₀c (by
      have : b₀ ∈ R ⊓ centralizer (U : Set G) := by rw [hRC]; exact h
      exact this.2)
    rcases mem_or_inv_mul_mem_of_relIndex_two hRidx (hBR hb₀B) hb₀P hr with h | h
    · exact Subgroup.mem_sup_right h
    · have : r = b₀ * (b₀⁻¹ * r) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hb₀B) (Subgroup.mem_sup_right h)
  refine ⟨2, zpowers z, le_rfl, hR1.W_le_U, hR1.idx_Q, hR1.idx_W, hR1.cent_y, hR1.comm_UB, ?_,
    hgen, hSC⟩
  rw [relIndex_blockZ_isAltType3 h3]
  norm_num

end C56

end CFSG.QuasithinUnique
