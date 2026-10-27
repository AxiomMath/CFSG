module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatBS

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.BlueprintB2
open scoped commutatorElement MatrixGroups

namespace C56

variable {G : Type} [Group G] [Finite G]

theorem baumann_Lin2_single {R H L : Subgroup G} (hmin : IsMinimalParabolic R H)
    (hblk : IsChi0Block H L) {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n)
    (hth : ⁅L, thompsonJ R⁆ = L) (hHLR : H = L ⊔ R) (hRN : R ≤ normalizer (L : Set G)) :
    IsSylowTwoOf (baum R) (L ⊔ baum R) ∧ baum R ≤ (baum R ⊓ L) ⊔ pCoreOf 2 (L ⊔ baum R) := by
  classical
  have hLs : IsShort2 L := hblk.1.1
  have hLH : L ≤ H := hblk.1.2.1
  have hR2 : IsPGroup 2 R := hmin.1.isPGroup
  have hRH : R ≤ H := hmin.1.le
  have hHN : H ≤ normalizer (L : Set G) := by
    rw [hHLR]; exact sup_le Subgroup.le_normalizer hRN
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hUH : blockU L ≤ H := hUL.trans hLH
  have hH2 : ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun g hg =>
    C1.exists_pow_mem_of_mem_sup hR2 hRN (hHLR ▸ hg)
  have hlin' := hlin
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin'
  let D : Lin2Data L F := ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hq
  have hF : 2 < Fintype.card F := by
    rw [hcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨M, ρ, φ, hset, hρL⟩ := exists_natQuotSetting hF D hLs hmin hLH hHLR hRN
  have hJ : ⁅elemThompsonIn 2 (R.subgroupOf H), (blockU L).subgroupOf H⁆ ≠ ⊥ := by
    intro hbot
    have hJU : thompsonJ R ≤ centralizer (blockU L : Set G) := by
      intro j hj
      rw [← elemThompsonIn_subgroupOf_map hRH] at hj
      obtain ⟨j', hj', rfl⟩ := hj
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hmem : ⁅j', (⟨u, hUH hu⟩ : ↥H)⁆ ∈
          ⁅elemThompsonIn 2 (R.subgroupOf H), (blockU L).subgroupOf H⁆ :=
        Subgroup.commutator_mem_commutator hj' (Subgroup.mem_subgroupOf.mpr hu)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact (congrArg Subtype.val hmem).symm
    have hJQ : thompsonJ R ≤ pCoreOf 2 H := by
      rw [← C1.inf_centralizer_blockU_eq hLs hLH hHN hH2]
      exact le_inf ((GammaExtra.thompsonJ_le_self R).trans hRH) hJU
    have hLQ : L ≤ blockQ L := by
      conv_lhs => rw [← hth]
      rw [Subgroup.commutator_le]
      intro l hl j hj
      have h1 := C1.commutator_mem_blockQ_of_mem_pCoreOf hLH hHN (hJQ hj) hl
      have : ⁅l, j⁆ = (j * l * j⁻¹ * l⁻¹)⁻¹ := by rw [commutatorElement_def]; group
      rw [this]; exact inv_mem h1
    have hα1 : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, A = 1 := by
      intro A
      obtain ⟨l, rfl⟩ := hαs A
      have hl : l ∈ α.ker := by rw [hαk]; exact (mem_blockQ_iff l).mp (hLQ l.2)
      exact hl
    have h1 := hα1 ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have h01 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simp at h01
  obtain ⟨ℓ, hSyl, -, -, hBρ, -, -, -, -⟩ := hset.Baumann_Sylow hJ
  rw [oddOrderSubgroup_top_eq hLs hHLR hR2 hRN hLH] at hSyl
  have hBmap := elemBaumannIn_subgroupOf_map hRH
  have hLmap : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hBR : baum R ≤ R := inf_le_left
  have hB2 : IsPGroup 2 (baum R) := hR2.to_le hBR
  have hSylG : IsSylowTwoOf (baum R) (L ⊔ baum R) := by
    obtain ⟨-, -, h3⟩ := hSyl
    refine ⟨le_sup_right, hB2, ?_⟩
    have := Subgroup.relIndex_map_map_of_injective (elemBaumannIn 2 (R.subgroupOf H))
      (L.subgroupOf H ⊔ elemBaumannIn 2 (R.subgroupOf H)) H.subtype_injective
    rw [Subgroup.map_sup, hLmap, hBmap] at this
    show ¬ 2 ∣ (baum R).relIndex (L ⊔ baum R)
    rw [this]
    exact h3
  refine ⟨hSylG, ?_⟩
  have hBN : baum R ≤ normalizer (L : Set G) := hBR.trans hRN
  have hBH : baum R ≤ H := hBR.trans hRH
  have hXH : L ⊔ baum R ≤ H := sup_le hLH hBH
  have hXN : L ⊔ baum R ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have hBL : ∀ (b : G) (hb : b ∈ baum R), ∃ l : ↥L, ρ ⟨b, hBH hb⟩ = ρ ⟨l, hLH l.2⟩ := by
    intro b hb
    have hbB : (⟨b, hBH hb⟩ : ↥H) ∈ elemBaumannIn 2 (R.subgroupOf H) := by
      have hb' := hb
      rw [← hBmap] at hb'
      obtain ⟨y, hy, hyb⟩ := hb'
      have : y = ⟨b, hBH hb⟩ := Subtype.ext hyb
      rwa [this] at hy
    have h1 : ρ ⟨b, hBH hb⟩ ∈ rootGamma ℓ := hBρ ▸ ⟨_, hbB, rfl⟩
    obtain ⟨A, hA⟩ := mem_slGamma_iff.mp (rootGamma_le_slGamma ℓ h1)
    obtain ⟨l, rfl⟩ := hαs A
    exact ⟨l, Subtype.ext (hA.trans (hρL l).symm)⟩
  let K₂ : Subgroup G := (L ⊔ baum R) ⊓ ρ.ker.map H.subtype
  have hK₂X : K₂ ≤ L ⊔ baum R := inf_le_left
  have hKconj : ∀ x ∈ L ⊔ baum R, ∀ k ∈ K₂, x * k * x⁻¹ ∈ K₂ := by
    intro x hx k hk
    have hxinv : x⁻¹ ∈ L ⊔ baum R := inv_mem hx
    have hprod : x * k * x⁻¹ ∈ L ⊔ baum R := mul_mem (mul_mem hx hk.1) hxinv
    refine ⟨hprod, ?_⟩
    obtain ⟨y, hy, hyk⟩ := hk.2
    have hyk' : (y : G) = k := hyk
    refine ⟨⟨x, hXH hx⟩ * y * ⟨x, hXH hx⟩⁻¹, (ρ.normal_ker).conj_mem y hy _, ?_⟩
    show x * (y : G) * x⁻¹ = x * k * x⁻¹
    rw [hyk']
  have hK₂N : L ⊔ baum R ≤ normalizer (K₂ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact ⟨fun hk => hKconj x hx k hk,
      fun hk => by simpa [mul_assoc] using hKconj x⁻¹ (inv_mem hx) _ hk⟩
  have hK₂2 : IsPGroup 2 K₂ := by
    intro g
    obtain ⟨y, hy, hyg⟩ := g.2.2
    obtain ⟨j, hj⟩ := C1.exists_pow_mem_of_mem_sup hB2 hBN g.2.1
    have hyg' : (y : G) = (g : G) := hyg
    have e : y ^ 2 ^ j = (⟨(g : G) ^ 2 ^ j, hLH hj⟩ : ↥H) :=
      Subtype.ext (by rw [Subgroup.coe_pow, hyg'])
    have h1 : ρ ⟨(g : G) ^ 2 ^ j, hLH hj⟩ = 1 := by
      rw [← e, map_pow, MonoidHom.mem_ker.mp hy, one_pow]
    have h2 : (⟨(g : G) ^ 2 ^ j, hj⟩ : ↥L) ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      apply slPerm_injective (k := F)
      rw [← hρL, map_one, h1]
      rfl
    rw [hαk] at h2
    have h3 : (g : G) ^ 2 ^ j ∈ blockQ L := (mem_blockQ_iff _).mpr h2
    obtain ⟨i, hi⟩ := C1.exists_pow_eq_one_of_isPGroup (C1.blockQ_isPGroup L) h3
    refine ⟨j + i, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow]
    show (g : G) ^ 2 ^ (j + i) = 1
    rw [pow_add, pow_mul]
    exact hi
  have hK₂P : K₂ ≤ pCoreOf 2 (L ⊔ baum R) := le_pCoreOf_of_normalizes hK₂X hK₂N hK₂2
  intro b hb
  obtain ⟨l, hl⟩ := hBL b hb
  have hbX : b ∈ L ⊔ baum R := Subgroup.mem_sup_right hb
  have hlX : (l : G) ∈ L ⊔ baum R := Subgroup.mem_sup_left l.2
  have hkX : b * (l : G)⁻¹ ∈ L ⊔ baum R := mul_mem hbX (inv_mem hlX)
  have hk : b * (l : G)⁻¹ ∈ K₂ := by
    refine ⟨hkX, ?_⟩
    refine ⟨⟨b, hBH hb⟩ * ⟨l, hLH l.2⟩⁻¹, ?_, rfl⟩
    show (⟨b, hBH hb⟩ * ⟨l, hLH l.2⟩⁻¹ : ↥H) ∈ ρ.ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl, mul_inv_cancel]
  have hkP : b * (l : G)⁻¹ ∈ pCoreOf 2 (L ⊔ baum R) := hK₂P hk
  have hkB : b * (l : G)⁻¹ ∈ baum R := hSylG.pCoreOf_le hkP
  have hlB : (l : G) ∈ baum R := by
    have := mul_mem (inv_mem hkB) hb
    have e : (b * (l : G)⁻¹)⁻¹ * b = (l : G) := by group
    rwa [e] at this
  have key : (b * (l : G)⁻¹) * (l : G) ∈ pCoreOf 2 (L ⊔ baum R) ⊔ (baum R ⊓ L) :=
    Subgroup.mul_mem_sup hkP ⟨hlB, l.2⟩
  rw [sup_comm] at key
  simpa using key

end C56

end CFSG.QuasithinUnique
